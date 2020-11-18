module Main where

import AST
import Context
import Pretty
import Type

main :: IO ()
main = mapM_ run [
     ("eid", eid),
     ("eid_client_unit", eid_client_unit),
     ("idunit", idunit),
     ("idid", idid),
     ("idclientunit", idclientunit),
     ("monoidclientunit", monoidclientunit),
     ("idclientunitnotype", idclientunitnotype),
     ("impredicative_ididunit",impredicative_ididunit)
  ]

run (name, eid) =
  let (polytype, context) = typesynthClosed eid
      str_eid      = pretty eid
      str_context  = pretty context
      str_polytype = pretty polytype
  in do
    putStrLn $ "Name: " ++ name
    putStrLn $ "Expr: " ++ str_eid
    putStrLn $ "Type: " ++ str_polytype
    putStrLn $ "Context: " ++ str_context
    putStrLn ""
