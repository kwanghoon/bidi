{-# LANGUAGE DataKinds, GADTs, KindSignatures, StandaloneDeriving #-}
-- | Abstract syntax
module AST where
import Control.Applicative
import Data.Monoid
import Data.Semigroup
import Data.Set(Set)
import qualified Data.Set as S

-- | Locations
data Loc
  = Client            -- c
  | Server            -- s
  | Unknown LVar      -- l
  | UnknownExists LVar -- l^
  deriving (Eq, Show)

-- | Expressions
data Expr
  = EVar Var            -- ^ x
  | EUnit               -- ^ ()
  | EAbs Var Loc Expr   -- ^ \x @ loc. e
  | ELocAbs LVar Expr   -- ^ /\l. e
  | EApp Expr Expr      -- ^ e1 e2
  | ELocApp Expr Loc      -- ^ e loc
  | EAnno Expr Polytype -- ^ e : A
  deriving (Eq, Show)

-- | subst e' x e = [e'/x]e
subst :: Expr -> Var -> Expr -> Expr
subst e' x expr = case expr of
  EVar x'       | x' == x   -> e'
                | otherwise -> EVar x'
  EUnit                     -> EUnit
  EAbs x' loc e | x' == x   -> EAbs x' loc e
                | otherwise -> EAbs x' loc (subst e' x e)
  ELocAbs l e               -> ELocAbs l (subst e' x e)
  EApp e1 e2                -> EApp (subst e' x e1) (subst e' x e2)
  ELocApp e loc             -> ELocApp (subst e' x e) loc
  EAnno e t                 -> EAnno (subst e' x e) t

-- Smart constructors
var :: String -> Expr
var = EVar . Var
eunit :: Expr
eunit = EUnit
eabs :: String -> Loc -> Expr -> Expr
eabs = EAbs . Var
elocabs :: String -> Expr -> Expr
elocabs = ELocAbs . LocVar
infixr 1 $$
($$) :: Expr -> Expr -> Expr
($$) = EApp
($@) :: Expr -> Loc -> Expr
($@) = ELocApp
(-:) :: Expr -> Polytype -> Expr
(-:) = EAnno

newtype Var  = Var     String deriving (Eq, Ord, Show)
newtype TVar = TypeVar String deriving (Eq, Ord, Show)

newtype LVar = LocVar  String deriving (Eq, Ord, Show)

data TypeKind = Mono | Poly

-- | Types, indexed by their kind: Monotype or Polytype.
--   Only Polytypes can have foralls.
data Type :: TypeKind -> * where
  TUnit   :: Type a                                -- ^ ()
  TVar    :: TVar -> Type a                        -- ^ alpha
  TExists :: TVar -> Type a                        -- ^ alpha^
  TForall :: TVar -> Type Poly -> Type Poly        -- ^ forall alpha. A
  TFun    :: Type a -> Loc -> Type a -> Type a     -- ^ A -loc-> B
  LForall :: LVar -> Type Poly -> Type Poly        -- ^ forall loc. A
deriving instance Show (Type a)
deriving instance Eq (Type a)

-- Smart constructors
tunit :: Type a
tunit = TUnit
tvar :: String -> Type a
tvar = TVar . TypeVar
exists :: String -> Type a
exists = TExists . TypeVar
tforall :: String -> Polytype -> Polytype
tforall = TForall . TypeVar
(-->) :: Type a -> Loc -> Type a -> Type a
(-->) = TFun
infixr 1 -->

tforalls :: [TVar] -> Polytype -> Polytype
tforalls = flip (foldr TForall)

lvar :: String -> Loc
lvar = Unknown . LocVar 
lexists :: String -> Loc
lexists = UnknownExists . LocVar
lforall :: String -> Polytype -> Polytype
lforall = LForall . LocVar

type Polytype = Type Poly
type Monotype = Type Mono

just :: Loc -> Maybe Loc
just loc = Just loc

-- | Is the type a Monotype?
monotype :: Type a -> Maybe Monotype
monotype typ = case typ of
  TUnit           -> Just TUnit
  TVar v          -> Just $ TVar v
  TForall _ _     -> Nothing
  TExists v       -> Just $ TExists v
  TFun t1 loc t2  -> TFun <$> monotype t1 <*> just loc <*> monotype t2
  LForall _ _     -> Nothing

-- | Any type is a Polytype since Monotype is a subset of Polytype
polytype :: Type a -> Polytype
polytype typ = case typ of
  TUnit          -> TUnit
  TVar v         -> TVar v
  TForall v t    -> TForall v t
  TExists v      -> TExists v
  TFun t1 loc t2 -> TFun (polytype t1) loc (polytype t2)
  LForall loc t  -> LForall loc t   -- polytype t ???

-- | The free type variables in a type
freeTVars :: Type a -> Set TVar
freeTVars typ = case typ of
  TUnit        -> mempty
  TVar v       -> S.singleton v
  TForall v t  -> S.delete v $ freeTVars t
  TExists v    -> S.singleton v
  TFun t1 _ t2 -> freeTVars t1 `mappend` freeTVars t2
  LForall l t  -> freeTVars t

-- | The free location variables in a type
freeLVars :: Type a -> Set LVar
freeLVars typ = case typ of
  TUnit          -> mempty
  TVar v         -> mempty
  TForall v t    -> freeLVars t
  TExists v      -> mempty
  TFun t1 loc t2 -> freeLVarsIn loc 
  LForall l t    -> S.delete l $ freeLVars t

-- | The free location variables in a location
freeLVarsIn :: Loc -> Set LVar
freeLVarsIn loc = case loc of
  Client          -> mempty
  Server          -> mempty
  Unknown l       -> S.singleton l
  UnknownExists l -> S.singleton l

-- | typeSubst A α B = [A/α]B
typeSubst :: Type a -> TVar -> Type a -> Type a
typeSubst t' v typ = case typ of
  TUnit                      -> TUnit
  TVar v'        | v' == v   -> t'
                 | otherwise -> TVar v'
  TForall v' t   | v' == v   -> TForall v' t
                 | otherwise -> TForall v' (typeSubst t' v t)
  TExists v'     | v' == v   -> t'
                 | otherwise -> TExists v'
  TFun t1 loc t2             -> TFun (typeSubst t' v t1) loc (typeSubst t' v t2)
  LForall l t                -> LForall l (typeSubst t' v t)

typeSubsts :: [(Type a, TVar)] -> Type a -> Type a
typeSubsts = flip $ foldr $ uncurry typeSubst

-- | locSubst loc l B = [loc/l]B
locSubst :: Loc -> LVar -> Type a -> Type a
locSubst loc' l typ = case typ of
  TUnit                     -> TUnit
  TVar v'                   -> TVar v'
  TForall v' t              -> TForall v' (locSubst loc' l t)
  TExists v'                -> TExists v'
  TFun t1 loc t2            -> TFun (locSubst loc' l t1) (locLocSubst loc' l loc) (locSubst loc' l t2)
  LForall l' t  | l' == l   -> LForall l' t
                | otherwise -> LForall l' (locSubst loc' l t)

-- | locLocSubst loc l loc0 = [loc/l]loc0
locLocSubst loc' l loc0 = case loc0 of
  Client                       -> Client
  Server                       -> Server
  Unknown l'       | l' == l   -> loc'
                   | otherwise -> Unknown l'
  UnknownExists l' | l' == l   -> loc'
                   | otherwise -> UnknownExists l'

-- | locExprSubst loc l e = [loc/l]e
locExprSubst loc' l e = case e of 
  EVar v -> EVar v
  EUnit -> EUnit
  EAbs v loc0 e0 -> EAbs v (locLocSubst loc' l loc0) (locExprSubst loc' l e0)
  ELocAbs l0 e0 | l0 == l   -> ELocAbs l0 e0
                | otherwise -> ELocAbs l0 (locExprSubst loc' l e0)
  EApp e1 e2     -> EApp (locExprSubst loc' l e1) (locExprSubst loc' l e2)
  ELocApp e loc  -> ELocApp (locExprSubst loc' l e) (locLocSubst loc' l loc)
  EAnno e ty     -> EAnno (locExprSubst loc' l e) (locSubst loc' l ty)

data ContextKind = Complete | Incomplete

-- | Context elements, indexed by their kind: Complete or Incomplete.
--   Only Incomplete contexts can have unsolved existentials.
data ContextElem :: ContextKind -> * where
  CForall        :: TVar -> ContextElem a             -- ^ alpha
  CVar           :: Var -> Polytype -> ContextElem a  -- ^ x : A
  CExists        :: TVar -> ContextElem Incomplete    -- ^ alpha^
  CExistsSolved  :: TVar -> Monotype -> ContextElem a -- ^ alpha^ = tau
  CMarker        :: TVar -> ContextElem a             -- ^ |> alpha^

  CLForall       :: LVar -> ContextElem a             -- ^ l
  CLExists       :: LVar -> ContextElem Incomplete    -- ^ l^
  CLExistsSolved :: LVar -> Loc -> ContextElem a      -- ^ l^ = loc
  CLMarker       :: LVar -> ContextElem a             -- ^ |> l^
deriving instance Eq (ContextElem a)
deriving instance Show (ContextElem a)

newtype GContext a      = Context [ContextElem a]
type CompleteContext = GContext Complete
type Context         = GContext Incomplete

-- | Snoc
(>:) :: GContext a -> ContextElem a -> GContext a
Context gamma >: x = Context $ x : gamma

-- | Context & list of elems append
(>++) :: GContext a -> [ContextElem a] -> GContext a
gamma >++ elems = gamma <> context elems

context :: [ContextElem a] -> GContext a
context = Context . reverse

dropMarker :: ContextElem a -> GContext a -> GContext a
dropMarker m (Context gamma) = Context $ tail $ dropWhile (/= m) gamma

breakMarker :: ContextElem a -> GContext a -> (GContext a, GContext a)
breakMarker m (Context xs) = let (r, _:l) = break (== m) xs in (Context l, Context r)

instance Monoid (GContext a) where
  mempty = Context []
  mappend (Context gamma) (Context delta) = Context (delta ++ gamma)

instance Semigroup (GContext a) where
  (Context gamma) <> (Context delta) = Context (delta ++ gamma)
