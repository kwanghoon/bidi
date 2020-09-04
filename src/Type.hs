{-# LANGUAGE GADTs #-}
-- | Bidirectional typechecking for higher-rank polymorphism
--   Implementation of http://www.mpi-sws.org/~neelk/bidir.pdf
module Type where

import Control.Applicative
import Control.Monad
import Data.Maybe
import Data.Monoid
import qualified Data.Set as S

import AST
import Context
import NameGen
import Pretty

-- | Algorithmic sublocation:
subloc :: Context -> Loc -> Loc -> NameGen Context
subloc gamma loc1 loc2 = 
  traceNS "subloc" (gamma, loc1, loc2) $
  checkwfloc gamma loc1 $ checkwfloc gamma loc2 $ 
    case (loc1, loc2) of
    -- <:Loc
    (Client, Client) -> return gamma
    (Server, Server) -> return gamma
    -- <:LVar
    (Unknown l1, Unknown l2) | l1 == l2 -> return gamma
    -- <:ExLVar
    (UnknownExists l1, UnknownExists l2) | l1 == l2 -> return gamma
    (UnknownExists l, loc) | l `S.notMember` freeLVarsIn loc -> 
      instantiateLocL gamma l loc
    (loc, UnknownExists l) | l `S.notMember` freeLVarsIn loc ->
      instantiateLocR gamma loc l
    _ -> error $ "subloc, don't know what to do with: "
                          ++ pretty (gamma, loc1, loc2)

-- | Algorithmic subtyping:
--   subtype Γ A B = Δ <=> Γ |- A <: B -| Δ
subtype :: Context -> Polytype -> Polytype -> NameGen Context
subtype gamma typ1 typ2 =
  traceNS "subtype" (gamma, typ1, typ2) $
  checkwftype gamma typ1 $ checkwftype gamma typ2 $
    case (typ1, typ2) of
    -- <:Var
    (TVar alpha, TVar alpha') | alpha == alpha' -> return gamma
    -- <:Unit
    (TUnit, TUnit) -> return gamma
    -- <:Exvar
    (TExists alpha, TExists alpha')
      | alpha == alpha' && alpha `elem` existentials gamma -> return gamma
    -- <:->
    (TFun a1 loc1 a2, TFun b1 loc2 b2) -> do
      theta <- subtype gamma b1 a1
      delta <- subtype theta (apply theta a2) (apply theta b2)
      subloc delta (lapply delta loc1) (lapply delta loc2)

    -- <:forallR
    (a, TForall alpha b) -> do
      -- Do alpha conversion to avoid clashes
      alpha' <- freshTVar
      dropMarker (CForall alpha') <$>
        subtype (gamma >: CForall alpha') a (typeSubst (TVar alpha') alpha b)

    -- <:forallLocR
    (loc, LForall l b) -> do 
      -- Do alpha conversion to avoid clashes
      l' <- freshLVar
      dropMarker (CLForall l') <$>
        subtype (gamma >: CLForall l') b (locSubst (UnknownExists l') l b)

    -- <:forallL
    (TForall alpha a, b) -> do
      -- Do alpha conversion to avoid clashes
      alpha' <- freshTVar
      dropMarker (CMarker alpha') <$>
        subtype (gamma >++ [CMarker alpha', CExists alpha'])
                (typeSubst (TExists alpha') alpha a)
                b

    -- <:forallLocL
    (LForall l a, b) -> do
      -- Do alpha conversion to avoid clashes
      l' <- freshLVar 
      dropMarker (CLMarker l') <$> 
        subtype (gamma >++ [CLMarker l', CLExists l'])
               (locSubst (UnknownExists l') l a)
               b

    -- <:InstantiateL
    (TExists alpha, a) | alpha `elem` existentials gamma
                      && alpha `S.notMember` freeTVars a ->
      instantiateL gamma alpha a

    -- <:InstantiateR
    (a, TExists alpha) | alpha `elem` existentials gamma
                      && alpha `S.notMember` freeTVars a ->
      instantiateR gamma a alpha
    _ -> error $ "subtype, don't know what to do with: "
                           ++ pretty (gamma, typ1, typ2)

-- | Algorithmic instantiation (left):
--   instantiateL Γ α A = Δ <=> Γ |- α^ :=< A -| Δ
instantiateL :: Context -> TVar -> Polytype -> NameGen Context
instantiateL gamma alpha a =
  traceNS "instantiateL" (gamma, alpha, a) $
  checkwftype gamma a $ checkwftype gamma (TExists alpha) $
  case solve gamma alpha =<< monotype a of
    -- InstLSolve
    Just gamma' -> return gamma'
    Nothing -> case a of
      -- InstLReach
      TExists beta 
        | ordered gamma alpha beta ->
            return $ fromJust $ solve gamma beta (TExists alpha)
        | otherwise ->
            return $ fromJust $ solve gamma alpha (TExists beta)
      -- InstLArr
      TFun a1 loc a2   -> do
        alpha1 <- freshTVar
        alpha2 <- freshTVar
        l      <- freshLVar
        theta <- instantiateR (insertAt gamma (CExists alpha) $ context
                                [ CLExists l
                                , CExists alpha2
                                , CExists alpha1
                                , CExistsSolved alpha $ TFun (TExists alpha1)
                                                             (UnknownExists l)
                                                             (TExists alpha2)
                                ])
                              a1 alpha1
        delta <- instantiateL theta alpha2 (apply theta a2)
        instantiateLocL delta l (lapply delta loc)
      -- InstLAIIR
      TForall beta b -> do
        -- Do alpha conversion to avoid clashes
        beta' <- freshTVar
        dropMarker (CForall beta') <$>
          instantiateL (gamma >++ [CForall beta'])
                       alpha
                       (typeSubst (TVar beta') beta b)
      _ -> error $ "The impossible happened! instantiateL: "
                ++ pretty (gamma, alpha, a)

-- | Algorithmic instantiation location (left):
--   instantiateLocL Γ l loc = Δ <=> Γ |- l^ :=< loc -| Δ
instantiateLocL gamma l loc = 
  traceNS "instantiateLocL" (gamma, l, loc) $
  checkwfloc gamma loc $ checkwfloc gamma (UnknownExists l) $
  case lsolve gamma l loc of
  -- InstLSolve
  Just gamma' -> return gamma'
  Nothing -> case loc of
    -- InstLReach
    UnknownExists l'
      | lordered gamma l l' ->
          return $ fromJust $ lsolve gamma l' (UnknownExists l)
      | otherwise ->
          return $ fromJust $ lsolve gamma l (UnknownExists l')
    _ -> error $ "The impossible happened! instantiateLocL: "
              ++ pretty (gamma, l, loc)

-- | Algorithmic instantiation (right):
--   instantiateR Γ A α = Δ <=> Γ |- A =:< α -| Δ
instantiateR :: Context -> Polytype -> TVar -> NameGen Context
instantiateR gamma a alpha =
  traceNS "instantiateR" (gamma, a, alpha) $
  checkwftype gamma a $ checkwftype gamma (TExists alpha) $
  case solve gamma alpha =<< monotype a of
    Just gamma' -> return gamma'
    Nothing -> case a of
      -- InstRReach
      TExists beta 
        | ordered gamma alpha beta ->
            return $ fromJust $ solve gamma beta (TExists alpha)
        | otherwise ->
            return $ fromJust $ solve gamma alpha (TExists beta)
      -- InstRArr
      TFun a1 loc a2   -> do
        alpha1 <- freshTVar
        alpha2 <- freshTVar
        l      <- freshLVar
        theta <- instantiateL (insertAt gamma (CExists alpha) $ context
                                 [ CLExists l
                                 , CExists alpha2
                                 , CExists alpha1
                                 , CExistsSolved alpha $ TFun (TExists alpha1)
                                                              (UnknownExists l)
                                                              (TExists alpha2)
                                 ])
                              alpha1
                              a1
        instantiateR theta (apply theta a2) alpha2
      -- InstRAIIL
      TForall beta b -> do
        -- Do alpha conversion to avoid clashes
        beta' <- freshTVar
        dropMarker (CMarker beta') <$>
          instantiateR (gamma >++ [CMarker beta', CExists beta'])
                       (typeSubst (TExists beta') beta b)
                       alpha
      _ -> error $ "The impossible happened! instantiateR: "
                ++ pretty (gamma, a, alpha)

-- | Algorithmic instantiation location (right):
--   instantiateLocR Γ loc l = Δ <=> Γ |- loc =:< l -| Δ
instantiateLocR gamma loc l = 
  traceNS "instantiateLocR" (gamma, loc, l) $ 
  checkwfloc gamma loc $ checkwfloc gamma (UnknownExists l) $ 
  case lsolve gamma l loc of 
    Just gamma' -> return gamma'
    Nothing -> case loc of
      -- InstRReach
      UnknownExists l'
        | lordered gamma l l' -> 
            return $ fromJust $ lsolve gamma l' (UnknownExists l)
        | otherwise ->
            return $ fromJust $ lsolve gamma l (UnknownExists l')
      _ -> error $ "The impossible happened! instantiateLocR: "
                ++ pretty (gamma, loc, l)

-- | Type checking:
--   typecheck Γ loc e A = Δ <=> Γ |-_loc e <= A -| Δ
typecheck :: Context -> Loc -> Expr -> Polytype -> NameGen Context
typecheck gamma loc expr typ =
  traceNS "typecheck" (gamma, loc, expr, typ) $
  checkwftype gamma typ $ case (expr, typ) of
    -- 1I
    (EUnit, TUnit) -> return gamma
    -- ForallI
    (e, TForall alpha a) -> do
      -- Do alpha conversion to avoid clashes
      alpha' <- freshTVar
      dropMarker (CForall alpha') <$>
        typecheck (gamma >: CForall alpha') loc e (typeSubst (TVar alpha') alpha a)
    -- LForallI 
    (e, LForall l a) -> do
      -- Do alpha conversion to avoid clashes
      l' <- freshLVar
      dropMarker (CLForall l') <$>
        typecheck (gamma >: CLForall l') loc (locExprSubst (Unknown l') l e) (locSubst (Unknown l') l a)
    -- ->I
    (EAbs x loc0 e, TFun a loc' b) -> do
      x' <- freshVar
      gamma0 <- subloc gamma loc' loc0
      dropMarker (CVar x' a) <$>
        typecheck (gamma0 >: CVar x' a) loc0 (subst (EVar x') x e) b
    -- Sub
    (e, b) -> do
      (a, theta) <- typesynth gamma loc e
      subtype theta (apply theta a) (apply theta b)

-- | Type synthesising:
--   typesynth Γ loc e = (A, Δ) <=> Γ |- e => A -| Δ
typesynth :: Context -> Loc -> Expr -> NameGen (Polytype, Context)
typesynth gamma loc expr = traceNS "typesynth" (gamma, loc, expr) $ checkwf gamma $
  case expr of
    -- Var
    EVar x -> return
      ( fromMaybe (error $ "typesynth: not in scope " ++ pretty (expr, gamma))
                  (findVarType gamma x)
      , gamma
      )
    -- Anno
    EAnno e a -> do
      delta <- typecheck gamma loc e a
      return (a, delta)
    -- 1I=>
    EUnit -> return (TUnit, gamma)
    -- {-
    -- ->I=> Original rule
    EAbs x loc0 e -> do
      x'    <- freshVar
      alpha <- freshTVar
      beta  <- freshTVar
      delta <- dropMarker (CVar x' (TExists alpha)) <$>
        typecheck (gamma >++ [ CExists alpha
                             , CExists beta
                             , CVar x' (TExists alpha)
                             ])
                  loc0
                  (subst (EVar x') x e)
                  (TExists beta)
      return (TFun (TExists alpha) loc0 (TExists beta), delta)
    -- -}
    {-
    -- ->I=> Full Damas-Milner type inference
    EAbs x loc0 e -> do
      x'    <- freshVar
      alpha <- freshTVar
      beta  <- freshTVar
      l     <- freshLVar
      (delta, delta')  <- breakMarker (CMarker alpha) <$>
        typecheck (gamma >++ [ CLExistsSolved l loc0
                             , CMarker alpha
                             , CExists alpha
                             , CExists beta
                             , CVar x' (TExists alpha)
                             ])
                  loc0
                  (subst (EVar x') x e)
                  (TExists beta)
      let tau = apply delta' (TFun (TExists alpha) (UnknownExists l) (TExists beta))
      let evars = unsolved delta'
      uvars <- replicateM (length evars) freshTVar
      return ( tforalls uvars $ typeSubsts (zip (map TVar uvars) evars) tau
             , delta)
    -}
    -- ->E
    EApp e1 e2 -> do
      (a, theta) <- typesynth gamma loc e1
      typeapplysynth theta loc (apply theta a) e2

-- | Type application synthesising
--   typeapplysynth Γ loc A e = (C, Δ) <=> Γ |- A . e =>> C -| Δ
typeapplysynth :: Context -> Loc -> Polytype -> Expr -> NameGen (Polytype, Context)
typeapplysynth gamma loc typ e = traceNS "typeapplysynth" (gamma, loc, typ, e) $
  checkwftype gamma typ $
  case typ of
    -- ForallApp
    TForall alpha a -> do
      -- Do alpha conversion to avoid clashes
      alpha' <- freshTVar
      typeapplysynth (gamma >: CExists alpha') loc
                     (typeSubst (TExists alpha') alpha a)
                     e
    -- ForallApp
    LForall l a -> do
      -- Do alpha conversion to avoid clashes
      l' <- freshLVar
      typeapplysynth (gamma >: CLExists l') loc 
                     (locSubst (UnknownExists l') l a)
                     e
    -- alpha^App
    TExists alpha -> do
      alpha1 <- freshTVar
      alpha2 <- freshTVar
      l      <- freshLVar
      delta <- typecheck (insertAt gamma (CExists alpha) $ context
                            [ CLExists l
                            , CExists alpha2
                            , CExists alpha1
                            , CExistsSolved alpha $ TFun (TExists alpha1)
                                                         (UnknownExists l)
                                                         (TExists alpha2)
                            ])
                         loc
                         e
                         (TExists alpha1)
      return (TExists alpha2, delta)
    -- ->App
    TFun a loc' c -> do
      delta <- typecheck gamma loc e a
      return (c, delta)

    _ -> error $ "typeapplysynth: don't know what to do with: "
              ++ pretty (gamma, loc, typ, e)

typesynthClosed :: Expr -> (Polytype, Context)
typesynthClosed e = let (a, gamma) = evalNameGen $ typesynth mempty Client e
                     in (apply gamma a, gamma)

-- Examples
eid :: Expr -- (λx @ l. x) : ∀ t. t → t
eid = eabs "x" (lvar "l") (var "x") -: lforall "l" (tforall "t" (tvar "t" --> lvar "l" $ tvar "t"))
-- Impredicative, so doesn't typecheck
ididunit :: Expr -- (λid. id id ()) ((λx. x) : ∀ t. t → t)
ididunit = eabs "id" (lvar "l1") (((var "id" -: tforall "t" (tvar "t" --> lvar "l" $ tvar "t"))  $$ var "id") $$ eunit) $$ eid
idunit :: Expr -- (λid. id ()) ((λx. x) : ∀ t. t → t)
idunit = eabs "id" (lvar "l") (var "id" $$ eunit) $$ eid
idid :: Expr -- id id
idid = (eid $$ eid) -: tforall "t" (tvar "t" --> lvar "l" $ tvar "t")
