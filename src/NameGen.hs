-- | Name generation
module NameGen where
import Control.Monad.State

import AST
import Pretty

import Debug.Trace

data NameState = NameState
  { varNames  :: [Var]
  , tvarNames :: [TVar]
  , indent    :: Int -- This has no place here, but useful for debugging
  }

initialNameState :: NameState
initialNameState = NameState
  { varNames  = map (Var . ('$':)) namelist
  , tvarNames = map (TypeVar . ('\'':)) namelist
  , indent    = 0
  }
  where
    namelist = [1..] >>= flip replicateM ['a'..'z']

type NameGen a = State NameState a

evalNameGen :: NameGen a -> a
evalNameGen = flip evalState initialNameState

-- | Create a fresh variable
freshVar :: NameGen Var
freshVar = do
  vvs <- gets varNames
  case vvs of
    (v:vs) -> do 
      modify $ \s -> s {varNames = vs}
      return v
    [] -> error "No fresh variable can be created."

-- | Create a fresh type variable
freshTVar :: NameGen TVar
freshTVar = do
  vvs <- gets tvarNames
  case vvs of
    (v:vs) -> do
      modify $ \s -> s {tvarNames = vs}
      return v
    [] -> error "No fresh type variable can be created."

-- | Print some debugging info
traceNS :: (Pretty a, Pretty b) => String -> a -> NameGen b -> NameGen b
traceNS f args x = do
  ilevel <- gets indent
  let ind = replicate (ilevel * 3) ' '
  trace (ind ++ f ++ pretty args) $ do
    modify $ \s -> s {indent = ilevel + 1}
    res <- x
    modify $ \s -> s {indent = ilevel}
    trace (ind ++ "=" ++ pretty res) $ return res

traceSeq :: (Pretty a, Pretty b) => String -> a -> NameGen b -> NameGen b
traceSeq f args x = do
  trace (f ++ " " ++ pretty args) $
    do res <- x
       return res
