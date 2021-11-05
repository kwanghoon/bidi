{-# LANGUAGE GADTs #-}

{- ICFP 2019 : A Mechanical Formalization of Higher-Ranked Polymorphic Type Inference
   (by JINXU ZHAO, BRUNO C. D. S. OLIVEIRA, TOM SCHRIJVERS)
-}

module Worklist where

import AST
import NameGen
import Pretty

import Data.Maybe
import qualified Data.Set as S

--
data JudgChain                              -- w (omega)
  = Subty Polytype Polytype                 -- A <: B
  | Check Expr Polytype                     -- e <= A
  | Synth Expr TVar JudgChain               -- e =>a w
  | Typeapply Polytype Expr TVar JudgChain  -- A . e =>> a w
  
  | TypeResult Polytype
  deriving (Eq, Show)

type Worklist = [WorklistElem]   -- Gamma

data WorklistElem
  = WForall TVar          -- alpha
  | WExists TVar          -- alpha^
  | WVar Var Polytype     -- x : A
  | WJC JudgChain  -- w
  deriving (Eq, Show)

instance Pretty JudgChain where
  bpretty d jc =
    case jc of
      Subty ty1 ty2 -> bpretty d ty1 . showString " <: " . bpretty d ty2
      Check e ty -> bpretty d e . showString " <= " . bpretty d ty
      Synth e tvar jc -> bpretty d e . showString " =>_"
        . bpretty d (TVar tvar) . showString " " . bpretty d jc
      Typeapply ty e tvar jc -> bpretty d ty . showString " o "
        . bpretty d e . showString " =>>_" . bpretty d (TVar tvar)
        . showString " " . bpretty d jc
      TypeResult ty -> showString " result: " . bpretty d ty

instance Pretty WorklistElem where
  bpretty d wl =
    case wl of
      WForall tvar -> bpretty d (TExists tvar)
      WExists tvar -> bpretty d (TVar tvar)
      WVar v ty -> bpretty d (EVar v) . showString " : " . bpretty d ty
      WJC jc -> bpretty d jc

-- | algorithmic typing

alty :: Worklist -> NameGen Polytype
-- alty [] = return []

-- | (1) ~ (3)
alty tr@(WForall tvar : wl) =    -- (1) Gamma, a   ---> Gamma
  traceNS "(1)" tr $
  alty wl

alty tr@(WExists tvar : wl) =    -- (2) Gamma, a^  ---> Gamma
  traceNS "(2)" tr $
  alty wl

alty tr@(WVar var ty : wl) =     -- (3) Gamma, x:A ---> Gamma
  traceNS "(3)" tr $
  alty wl

-- (4) ~ (11)
alty tr@(WJC (Subty TUnit TUnit) : wl) =      -- (4) Gamma ||- 1 <: 1 ---> Gamma
  traceNS "(4)" tr $
  alty wl

alty tr@(WJC (Subty (TVar v1) (TVar v2)) : wl)       -- (5) Gamma ||- a <: a ---> Gamma
  | v1 == v2 =
      traceNS "(5)" tr $
      alty wl
  
alty tr@(WJC (Subty (TExists v1) (TExists v2)) : wl) -- (6) Gamma ||- a^ <: a^ ---> Gamma
  | v1 == v2 =
      traceNS "(6)" tr $
      alty wl

-- (7) Gamma ||- A1->A2 <: B1->B2 ---> Gamma ||- A2 <: B2 ||- B1 <: A1
alty tr@(WJC (Subty (TFun a1 a2) (TFun b1 b2)) : wl) 
  = traceNS "(7)" tr $
    alty (WJC (Subty b1 a1) : WJC (Subty a2 b2) : wl)

-- (8) Gamma ||- forall a.A <: B ---> Gamma, a^ ||- [a^/a]A <: B (when B != forall a.B')
alty tr@(WJC (Subty (TForall v a) b) : wl)
  | not (isTForall b) =
    traceNS "(8)" tr $
    do alpha <- freshTVar
       alty (WJC (Subty (typeSubst (TExists alpha) v a ) b)  : WExists alpha : wl)

-- (9) Gamma ||- a <: forall b.B ---> Gamma, b ||- A <: B
alty tr@(WJC (Subty a (TForall v b)) : wl) =
  traceNS "(9)" tr $
  do alpha <- freshTVar
     alty (WJC (Subty a (typeSubst (TVar alpha) v b)) : WForall alpha : wl)

-- (10) Gamma[a^] ||- a^ <: A->B ---> [a1^->a2^/a^](Gamma[a1^,a2^]) ||- a1^->a2^ <: A->B
--                                    (when a^ not in FV(A) U FV (B))
alty tr@(WJC (Subty (TExists v) (TFun a b)) : wl)
  |    v `elem` existentialsWL wl
    && v `S.notMember` freeTVars a
    && v `S.notMember` freeTVars b =

    traceNS "(10)" tr $
    do alpha1 <- freshTVar
       alpha2 <- freshTVar

       alty (typeSubstWL (TFun (TExists alpha1) (TExists alpha2)) v
             (WJC (Subty (TFun (TExists alpha1) (TExists alpha2)) (TFun a b))
              : insertAtWL wl (WExists v) [WExists alpha1, WExists alpha2]))

-- (11) Gamma[a^] ||- A->B <: a^ ---> [a1^->a2^/a^](Gamma[a1^,a2^]) ||- A->B <: a1^->a2^ 
--                                    (when a^ not in FV(A) U FV (B))
alty tr@(WJC (Subty (TFun a b) (TExists v)) : wl)
  |    v `elem` existentialsWL wl
    && v `S.notMember` freeTVars a
    && v `S.notMember` freeTVars b =

    traceNS "(11)" tr $
    do alpha1 <- freshTVar
       alpha2 <- freshTVar

       alty (typeSubstWL (TFun (TExists alpha1) (TExists alpha2)) v
             (WJC (Subty (TFun a b) (TFun (TExists alpha1) (TExists alpha2)))
              : insertAtWL wl (WExists v) [WExists alpha1, WExists alpha2]))

-- (12) Gamma[a^][b^] ||- a^ <: b^ ---> [a^/b^]( Gamma[a^][] )
-- (13) Gamma[a^][b^] ||- b^ <: a^ ---> [a^/b^]( Gamma[a^][] )

alty tr@(WJC (Subty (TExists alpha) (TExists beta)) : wl)
  | orderedWL wl alpha beta =
      traceNS "(12)" tr $
      alty (typeSubstWL (TExists alpha) beta
            (insertAtWL wl (WExists beta) []))
      
  | orderedWL wl beta alpha =
      traceNS "(13)" tr $
      alty (typeSubstWL (TExists alpha) beta
            (insertAtWL wl (WExists beta) []))

-- (14) Gamma[a][b^] ||- a <: b^ ---> [a/b^]( Gamma[a][] )
-- (15) Gamma[a][b^] ||- b^ <: a ---> [a/b^]( Gamma[a][] )

alty tr@(WJC (Subty (TVar alpha) (TExists beta)) : wl)
  | WForall alpha `elem` dropMarkerWL (WExists beta) wl =
      traceNS "(14)" tr $
      alty (typeSubstWL (TVar alpha) beta
            (insertAtWL wl (WExists beta) []))

alty tr@(WJC (Subty (TExists beta) (TVar alpha)) : wl)
  | WForall alpha `elem` dropMarkerWL (WExists beta) wl =
      traceNS "(15)" tr $
      alty (typeSubstWL (TVar alpha) beta
            (insertAtWL wl (WExists beta) []))

-- (16) Gamma[b^] ||- 1 <: b^ ---> [1/b^]( Gamma[] )
-- (17) Gamma[b^] ||- b^ <: 1 ---> [1/b^]( Gamma[] )

alty tr@(WJC (Subty TUnit (TExists beta)) : wl)
  | beta `elem` existentialsWL wl =
      traceNS "(16)" tr $
      alty (typeSubstWL TUnit beta
            (insertAtWL wl (WExists beta) []))

alty tr@(WJC (Subty (TExists beta) TUnit) : wl)
  | beta `elem` existentialsWL wl =
      traceNS "(17)" tr $
      alty (typeSubstWL TUnit beta
            (insertAtWL wl (WExists beta) []))

-- (18) Gamma ||- e <= b ---> Gamma ||- e =>_a a <: B
--      (when e not= lamx.e' and B not= forall a.B')
alty tr@(WJC (Check e b) : wl)
  | isAbs e == False && isTForall b == False =
      traceNS "(18)" tr $
      do alpha <- freshTVar
         alty (WJC (Synth e alpha (Subty (TVar alpha) b)) : wl)

-- (19) Gamma ||- e <= forall a.A ---> Gamma,a ||- e <= A
alty tr@(WJC (Check e (TForall alpha a)) : wl) =
  traceNS "(19)" tr $
  do alpha' <- freshTVar
     let a' = typeSubst (TVar alpha') alpha a
     alty (WJC (Check e a') : WForall alpha' : wl)

-- (20) Gamma ||- lam x.e <= A->B ---> Gamma, x:A ||- e <= B
alty tr@(WJC (Check (EAbs x e) (TFun a b)) : wl) =
  traceNS "(20)" tr $
  alty (WJC (Check e b) : (WVar x a) : wl)

-- (21) Gamma[a^] ||- lam x.e <= a^ --->
--      [a1^->a2^/a^](Gamma[a1^,a2^],x:a1^ ||- e <= a2^)
alty tr@(WJC (Check (EAbs x e) (TExists alpha)) : wl)
  | alpha `elem` existentialsWL wl = 
      traceNS "(21)" tr $
      do alpha1 <- freshTVar
         alpha2 <- freshTVar
         alty (typeSubstWL (TFun (TExists alpha1) (TExists alpha2)) alpha
           (WJC (Check e (TExists alpha2))
            : WVar x (TExists alpha1)
            : insertAtWL wl (WExists alpha) [WExists alpha1, WExists alpha2]))

-- (22) Gamma ||- x =>_a w ---> Gamma ||- [A/a]w  (when x:A in Gamma)
alty tr@(WJC (Synth (EVar x) alpha jc) : wl) = 
  traceNS "(22)" tr $
  case findVarType wl x of
    Just ty -> alty (typeSubstWL ty alpha (WJC jc : wl))
    Nothing -> error ("Var not found: " ++ show x)

-- (23) Gamma ||- (e : A) =>_a w ---> Gamma ||- [A/a]w ||- e <= A
alty tr@(WJC (Synth (EAnno e a) alpha jc) : wl) =
  traceNS "(23)" tr $
  alty (WJC (Check e a) : WJC (typeSubstJC a alpha jc) : wl)

-- (24) Gamma ||- () =>_a w ---> Gamma ||- [1/a]w
alty tr@(WJC (Synth EUnit  alpha jc) : wl) =
  traceNS "(24)" tr $
  alty (WJC (typeSubstJC TUnit alpha jc) : wl)

-- (25) Gamma ||- lam x.e =>_a w --->
--      Gamma,alpha^,beta^ ||- [alpha^->beta^/a]w, x:alpha^ ||- e <= beta^
alty tr@(WJC (Synth (EAbs x e) alpha jc) : wl) =
  traceNS "(25)" tr $
  do beta1 <- freshTVar
     beta2 <- freshTVar
     alty (WJC (Check e (TExists beta2)) : WVar x (TExists beta1)
           : WJC (typeSubstJC (TFun (TExists beta1) (TExists beta2)) alpha jc)
           : WExists beta2 : WExists beta1 : wl)


-- (26) Gamma ||- e1 e2 =>_a w ---> Gamma ||- e1 =>_b (b dot e_2 =>>_a w)
alty tr@(WJC (Synth (EApp e1 e2) alpha jc) : wl) =
  traceNS "(26)" tr $
  do beta <- freshTVar
     alty (WJC (Synth e1 beta (Typeapply (TVar beta) e2 alpha jc)) : wl)

-- (27) Gamma ||- forall b.A dot e =>>_a w --->
--      Gamma, a^ ||- [a^/b]A dot e =>>_a w
alty tr@(WJC (Typeapply (TForall beta ty) e alpha jc) : wl) =
  traceNS "(27)" tr $
  do beta1 <- freshTVar
     alty (WJC (Typeapply (typeSubst (TExists beta1) beta ty) e alpha jc)
           : WExists beta1 : wl)

-- (28) Gamma ||- A->C dot e =>>_a w ---> Gamma ||- [C/a]w ||- e <= A
alty tr@(WJC (Typeapply (TFun a c) e alpha jc) : wl) =
  traceNS "(28)" tr $
  alty (WJC (Check e a) : WJC (typeSubstJC c alpha jc) : wl)

-- (29) Gamma[a^] ||- b^ dot e =>>_a w --->
--      [a1^->a2^/a^](Gamma[a1^,a2^] ||- a1^->a2^ dot e =>>_a w)
alty tr@(WJC (Typeapply (TExists beta) e alpha jc) : wl)
  | beta `elem` existentialsWL wl =
      traceNS "(29)" tr $
      do alpha1 <- freshTVar
         alpha2 <- freshTVar
         alty (typeSubstWL (TFun (TExists alpha1) (TExists alpha2)) alpha
              (WJC (Typeapply (TFun (TExists alpha1) (TExists alpha2)) e alpha jc)
               : insertAtWL wl (WExists alpha) [WExists alpha1, WExists alpha2]))

-- Extra
alty tr@(WJC (TypeResult ty) : wl) =
  traceNS "(result)" tr $
  return ty

-- 
alty tr@wl =
  traceNS "somethin worng: " tr $
  error "Not implemented yet"


--
altyClosed :: Expr -> Polytype
altyClosed prog = evalNameGen $
  do alpha <- freshTVar
     alty [WJC (Synth prog alpha (TypeResult (TExists alpha)))]


-- isTForall a
isTForall :: Polytype -> Bool
isTForall (TForall _ _) = True
isTForall _ = False

isAbs (EAbs _ _) = True
isAbs _ = False


--
breakMarkerWL :: WorklistElem -> Worklist -> (Worklist, Worklist)
breakMarkerWL m w = bwlist m [] w
  where
    bwlist m rev_prev [] = (reverse rev_prev, [])
    bwlist m rev_prev (elem : w)
      | m == elem = (reverse rev_prev, w)
      | otherwise = bwlist m (elem : rev_prev) w
    
insertAtWL :: Worklist -> WorklistElem -> Worklist -> Worklist
insertAtWL w m new = prev ++ new ++ next
  where
    (prev, next) = breakMarkerWL m w

dropMarkerWL :: WorklistElem -> Worklist -> Worklist
dropMarkerWL m w = tail $ dropWhile (/= m) w

orderedWL :: Worklist -> TVar -> TVar -> Bool
orderedWL w alpha beta = alpha `elem` existentialsWL wL
  where
    wL = dropMarkerWL (WExists beta) w

existentialsWL :: Worklist -> [TVar]
existentialsWL [] = []
existentialsWL (WExists v : wl) = v : existentialsWL wl
existentialsWL (_ : wl) = existentialsWL wl

typeSubstWL :: Polytype -> TVar -> Worklist -> Worklist
typeSubstWL t' alpha w =
  case w of
    [] -> []
    (WForall beta : w') -> WForall beta : typeSubstWL t' alpha w'
    (WExists beta : w')
      | alpha == beta -> typeSubstWL t' alpha w' -- Todo: ???
      | otherwise -> WExists beta : typeSubstWL t' alpha w'
    (WVar x ty : w') -> WVar x (typeSubst t' alpha ty) : typeSubstWL t' alpha w'
    (WJC jc : w') -> WJC (typeSubstJC t' alpha jc) : typeSubstWL t' alpha w'

typeSubstJC :: Polytype -> TVar -> JudgChain -> JudgChain
typeSubstJC t' alpha jc =
  case jc of
    Subty a b -> Subty (typeSubst t' alpha a) (typeSubst t' alpha b)
    Check e ty -> Check e (typeSubst t' alpha ty)
    Synth e x jc -> Synth e x (typeSubstJC t' alpha jc)
    Typeapply a e x jc -> Typeapply (typeSubst t' alpha a) e x (typeSubstJC t' alpha jc)
    TypeResult ty -> TypeResult (typeSubst t' alpha ty)

findVarType :: Worklist -> Var -> Maybe Polytype
findVarType wl x = listToMaybe [t | WVar y t <- wl, x==y]
