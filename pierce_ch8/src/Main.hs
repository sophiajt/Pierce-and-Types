module Main where

import System.IO
import Data.List

data Type = TBool | TNat | TError deriving (Show, Eq)
data Term = TrueT | FalseT | If Term Term Term | Zero | 
            Succ Term | Pred Term | IsZero Term deriving (Show, Read, Eq) 
data Value = TrueValue | FalseValue | NV NumericValue | ErrorValue String deriving Show 
data NumericValue = ZeroNV | SuccNV NumericValue deriving Show 

can_step::Term->Bool
can_step t1 = let t1_new = eval t1 in (t1 /= t1_new)

eval::Term->Term
eval (If TrueT t2 _ ) = eval t2
eval (If FalseT _ t3) = eval t3
eval (If t1 t2 t3) = eval (If (eval t1) t2 t3)
eval TrueT  = TrueT
eval FalseT = FalseT
eval Zero = Zero
eval (Pred Zero) = Zero
eval (Pred (Succ t1)) = eval t1
eval (Pred t1) = if (can_step t1) then eval (Pred (eval t1)) else (Pred t1) 
eval (Succ t1) = if (can_step t1) then eval (Succ (eval t1)) else (Succ t1)
eval (IsZero Zero) = TrueT
eval (IsZero (Succ t1)) = FalseT
eval (IsZero t1) = if (can_step t1) then eval (IsZero (eval t1)) else (IsZero t1) 

typeCheck::Term->Type 
typeCheck TrueT = TBool
typeCheck FalseT = TBool
typeCheck Zero = TNat
typeCheck (Succ t1) = if (typeCheck t1) == TNat then TNat else TError 
typeCheck (Pred t1) = if (typeCheck t1) == TNat then TNat else TError
typeCheck (IsZero t1) = if (typeCheck t1) == TNat then TBool else TError
typeCheck (If t1 t2 t3) = if (typeCheck t1) == TBool then 
                            let t2_type = typeCheck t2 in
                              let t3_type = typeCheck t3 in
                                if (t2_type == t3_type) then t2_type else TError
                          else TError
                          
term_to_value::Term->Value
term_to_value x = 
    case x of TrueT   -> TrueValue
              FalseT  -> FalseValue
              Zero    -> NV ZeroNV
              Succ t1 -> let v = term_to_value t1 in
                           case v of NV nv -> NV (SuccNV nv)
                                     _     -> ErrorValue "Succ of non-numeric value"
              _       -> ErrorValue "Term can not evaluate to a value" 


eval_to_value::Term->Value
eval_to_value x = 
  let result = eval x in term_to_value result

prompt::(Show a, Read b, Show c, Read d) => (b->a) -> (d->c) -> IO()
prompt action action2 = do
  putStr "> "
  hFlush stdout
  input <- getLine
  if (input == "quit") then putStrLn "exiting..." else do 
    (putStrLn . show . action . read) input
    (putStrLn . show . action2 . read) input
    prompt action action2
    
main::IO()
main = 
  prompt typeCheck eval_to_value 
