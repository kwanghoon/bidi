module Main where

import AST
import Context
import NameGen
import Pretty
import Type
import Worklist

import System.Environment (getArgs, withArgs)

main :: IO ()
main =
  do args <- getArgs
     if "worklist" `elem` args
       then runAlty
       else runBidi

benchmark =
  [
    idnotype,
    idunitnotype,
    polyidunit,
    eid,
    idunit,
    idid,
    ididunit
  ]
  
runBidi = mapM_ run benchmark
  where
    run prog = 
      let (polytype, context) = typesynthClosed prog
          str_prog      = pretty prog
          str_context  = pretty context
          str_polytype = pretty polytype
      in do putStrLn $ "Expr: " ++ str_prog
            putStrLn $ "Type: " ++ str_polytype
            putStrLn $ "Context: " ++ str_context
            putStrLn ""

runAlty = mapM_ run benchmark
  where
    run prog =
      do let ty = altyClosed prog
         putStrLn $ "Expr : " ++ pretty prog
         putStrLn $ "Type : " ++ pretty ty
         
     
