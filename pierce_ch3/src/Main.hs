module Main where

import System.IO
import Data.List

data Type = TBool | TNat
data Term = TrueTerm | FalseTerm | If Term Term Term deriving (Show, Read) 
data Value = TrueValue | FalseValue | ErrorValue String deriving Show 

eval::Term->Term
eval (If TrueTerm t2 _ ) = eval t2
eval (If FalseTerm _ t3) = eval t3
eval (If t1 t2 t3) = eval (If (eval t1) t2 t3)
eval TrueTerm  = TrueTerm
eval FalseTerm = FalseTerm

eval_to_value::Term->Value
eval_to_value x = 
  let result = eval x in
    case result of TrueTerm  -> TrueValue
                   FalseTerm -> FalseValue
                   _         -> ErrorValue "Term can not evaluate to a value" 

prompt::(Show a, Read b) => (b->a) -> IO()
prompt action = do
  putStr "> "
  hFlush stdout
  input <- getLine
  if (input == "quit") then putStrLn "exiting..." else do 
    (putStrLn . show . action . read) input
    prompt action
    
main::IO()
main = 
  prompt eval_to_value
