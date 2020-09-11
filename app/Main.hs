module Main where

import AST
import Context
import Pretty
import Type

main :: IO ()
main = mapM_ run [eid, eid_client_unit, idunit, idid, idclientunit, monoidclientunit, ididunit]

run eid = 
  let (polytype, context) = typesynthClosed eid
      str_eid      = pretty eid
      str_context  = pretty context
      str_polytype = pretty polytype
  in do
    putStrLn $ "Expr: " ++ str_eid
    putStrLn $ "Type: " ++ str_polytype
    putStrLn $ "Context: " ++ str_context
    putStrLn ""
    
     
