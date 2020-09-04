{-# LANGUAGE GADTs, DataKinds #-}
-- | Some helpers for workingw ith contexts
module Context where
import Data.Maybe
import Data.Monoid

import AST
import Pretty

existentials :: Context -> [TVar]
existentials (Context gamma) = aux =<< gamma
  where aux (CExists alpha)         = [alpha]
        aux (CExistsSolved alpha _) = [alpha]
        aux _                       = []

lexistentials :: Context -> [LVar]
lexistentials (Context gamma) = aux =<< gamma
  where aux (CLExists l)           = [l]
        aux (CLExistsSolved l loc) = [l]
        aux  _                     = []

unsolved :: Context -> [TVar]
unsolved (Context gamma) = [alpha | CExists alpha <- gamma]

lunsolved :: Context -> [LVar]
lunsolved (Context gamma) = [l | CLExists l <- gamma]

vars :: Context -> [Var]
vars (Context gamma) = [x | CVar x _ <- gamma]

foralls :: Context -> [TVar]
foralls (Context gamma) = [alpha | CForall alpha <- gamma]

lforalls :: Context -> [LVar]
lforalls (Context gamma) = [l | CLForall l <- gamma]

markers :: Context -> [TVar]
markers (Context gamma) = [alpha | CMarker alpha <- gamma]

lmarkers :: Context -> [LVar]
lmarkers (Context gamma) = [l | CLMarker l <- gamma]

-- | Well-formedness of contexts
--   wf Γ <=> Γ ctx
wf :: Context -> Bool
wf (Context gamma) = case gamma of
  -- EmptyCtx
  [] -> True
  c:cs -> let gamma' = Context cs in wf gamma' && case c of
    -- UvarCtx
    CForall alpha -> alpha `notElem` foralls gamma'
    -- VarCtx
    CVar x a -> x `notElem` vars gamma' && typewf gamma' a
    -- EvarCtx
    CExists alpha -> alpha `notElem` existentials gamma'
    -- SolvedEvarCtx
    CExistsSolved alpha tau -> alpha `notElem` existentials gamma'
                            && typewf gamma' tau
    -- MarkerCtx
    CMarker alpha -> alpha `notElem` markers gamma'
                  && alpha `notElem` existentials gamma'

    -- CLForall
    CLForall l -> l `notElem` lforalls gamma'

    -- CLExists
    CLExists l -> l `notElem` lexistentials gamma'

    -- CLExistsSolved
    CLExistsSolved l loc -> l `notElem` lexistentials gamma'
                         && locwf gamma' loc

    -- CLMarker
    CLMarker l -> l `notElem` lmarkers gamma'
               && l `notElem` lexistentials gamma'

-- | Well-formedness of types
--   typewf Γ A <=> Γ |- A
typewf :: Context -> Type a -> Bool
typewf gamma typ = case typ of
  -- UvarWF
  TVar alpha -> alpha `elem` foralls gamma
  -- UnitWF
  TUnit -> True
  -- ArrowWF
  TFun a loc b -> typewf gamma a && typewf gamma b && locwf gamma loc
  -- ForallWF
  TForall alpha a -> typewf (gamma >: CForall alpha) a
  -- EvarWF and SolvedEvarWF
  TExists alpha -> alpha `elem` existentials gamma
  -- LForallWF
  LForall l a -> typewf (gamma >: CLForall l) a

-- | Well-formedness of locations
--   locwf Γ loc <=> Γ |- loc
locwf :: Context -> Loc -> Bool
locwf gamma loc = case loc of
  -- ClientWF
  Client -> True
  -- ServerWF
  Server -> True
  -- UnknownWF
  Unknown l -> l `elem` lforalls gamma
  -- UnknownExistWF
  UnknownExists l -> l `elem` lexistentials gamma
  

-- Assert-like functionality to make sure that contexts and types are
-- well-formed
checkwf :: Context -> x -> x
checkwf gamma x | wf gamma  = x
                | otherwise = error $ "Malformed context: " ++ pretty gamma

checkwftype :: Context -> Polytype -> x -> x
checkwftype gamma a x | typewf gamma a = checkwf gamma x
                      | otherwise      = error $ "Malformed type: "
                                       ++ pretty (a, gamma)

checkwfloc :: Context -> Loc -> x -> x
checkwfloc gamma a x | locwf gamma a = checkwf gamma x
                     | otherwise     = error $ "Malformed location: "
                                     ++ pretty (a, gamma)

-- | findSolved (ΓL,α^ = τ,ΓR) α = Just τ
findSolved :: Context -> TVar -> Maybe Monotype
findSolved (Context gamma) v = listToMaybe [t | CExistsSolved v' t <- gamma, v == v']

-- | findVarType (ΓL,x : A,ΓR) x = Just A
findVarType :: Context -> Var -> Maybe Polytype
findVarType (Context gamma) v = listToMaybe [t | CVar v' t <- gamma, v == v']

-- | findLSolved (ΓL,l^ = τ,ΓR) l = Just τ
findLSolved :: Context -> LVar -> Maybe Loc
findLSolved (Context gamma) l = listToMaybe [loc | CLExistsSolved l' loc <- gamma, l == l']

-- | solve (ΓL,α^,ΓR) α τ = (ΓL,α = τ,ΓR)
solve :: Context -> TVar -> Monotype -> Maybe Context
solve gamma alpha tau | typewf gammaL tau = Just gamma'
                      | otherwise         = Nothing
  where (gammaL, gammaR) = breakMarker (CExists alpha) gamma
        gamma' = gammaL >++ [CExistsSolved alpha tau] <> gammaR

-- | lsolve (ΓL,α^,ΓR) α τ = (ΓL,α = τ,ΓR)
lsolve :: Context -> LVar -> Loc -> Maybe Context
lsolve gamma l loc | locwf gammaL loc = Just gamma'
                   | otherwise        = Nothing
   where (gammaL, gammaR) = breakMarker (CLExists l) gamma
         gamma' = gammaL >++ [CLExistsSolved l loc] <> gammaR

-- | insertAt (ΓL,c,ΓR) c Θ = ΓL,Θ,ΓR
insertAt :: Context -> ContextElem Incomplete -> Context -> Context
insertAt gamma c theta = gammaL <> theta <> gammaR
  where (gammaL, gammaR) = breakMarker c gamma

-- | apply Γ A = [Γ]A
apply :: Context -> Polytype -> Polytype
apply gamma typ = case typ of
  TUnit           -> TUnit
  TVar v          -> TVar v
  TForall v t     -> TForall v (apply gamma t)
  TExists v       -> maybe (TExists v) (apply gamma . polytype) $ findSolved gamma v
  TFun t1 loc t2  -> apply gamma t1 `TFun` lapply gamma loc $ apply gamma t2
  LForall l t     -> LForall l (apply gamma t)

-- | lapply Γ loc = [Γ]loc
lapply :: Context -> Loc -> Loc
lapply gamma loc = case loc of
  Client -> Client
  Server -> Server
  Unknown l -> Unknown l
  UnknownExists l -> maybe (UnknownExists l) (\loc->loc) $ findLSolved gamma l
    
-- | ordered Γ α β = True <=> Γ[α^][β^]
ordered :: Context -> TVar -> TVar -> Bool
ordered gamma alpha beta =
  let gammaL = dropMarker (CExists beta) gamma
   in alpha `elem` existentials gammaL

-- | lordered Γ α β = True <=> Γ[α^][β^]
lordered :: Context -> LVar -> LVar -> Bool
lordered gamma l1 l2 =
  let gammaL = dropMarker (CLExists l2) gamma
   in l1 `elem` lexistentials gammaL
      
