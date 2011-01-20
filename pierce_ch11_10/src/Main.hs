module Main where

import System.IO
import Data.List

type Variable = String
type VarList = [(Variable, Int)]
type Context = [(Variable, Type)]

data Value = Lambda (Variable, Type, Term) | InlValue Value Type | InrValue Value Type | TrueValue | FalseValue | ErrorValue | ValueTerm Term deriving Show
data Type = TFun Type Type | TSum Type Type | TBool | TUnknown deriving (Show, Read, Eq)
data Term = Var Variable | Abs Variable Type Term | App Term Term | Inl Term Type | Inr Term Type | CaseInl Term Variable Term | CaseInr Term Variable Term | TrueT | FalseT | ErrorT deriving (Show, Read, Eq)

getVarType::Variable->Context->Type
getVarType name vars = 
  let f (vname, _) = (vname == name) in 
    let valueFound = find f vars in
       case valueFound of Just (name, typeId) -> typeId 
                          Nothing -> TUnknown

getVarName::Variable->VarList->Variable
getVarName name vars = 
  let f (vname, _) = (vname == name) in 
    let valueFound = find f vars in
       case valueFound of Just (name, id) -> name ++ (show id) 
                          Nothing -> name

uniquify::Term->VarList->Int->(Term, Int)
uniquify term vars lambdaId = 
  case term of Var var    -> (Var (getVarName var vars), lambdaId)
               Abs var type1 t2 -> 
                 let newLambdaId1 = lambdaId + 1 in 
                   let newVars = (var, lambdaId):vars in
                     let (uniqueBody, newLambdaId2) = uniquify t2 newVars newLambdaId1 in 
                       (Abs (getVarName var newVars) type1 uniqueBody, newLambdaId2)
               App t1 t2 ->
                 let (uniqueT1, newLambdaId1) = uniquify t1 vars lambdaId in
                   let (uniqueT2, newLambdaId2) = uniquify t2 vars newLambdaId1 in
                     (App uniqueT1 uniqueT2, newLambdaId2)
               t -> (t, lambdaId)
               
substitute::Variable->Term->Term->Term
substitute varName replaceTerm term = 
  case term of Var var          -> if var==varName then replaceTerm else term 
               Abs var type1 t2 -> Abs var type1 (substitute varName replaceTerm t2)
               App t1 t2        -> App (substitute varName replaceTerm t1) (substitute varName replaceTerm t2)

eval::Term->Term
eval (App (Abs var type1 t1) t2) = 
  let t2_eval = eval t2 in
    if t2_eval == t2 
      then eval (substitute var t2_eval t1) 
      else eval (App (Abs var type1 t1) (eval t2))
eval (App t1 t2) = eval (App (eval t1) t2)
eval (Inl t1 type1) = Inl (eval t1) type1
eval (Inr t1 type1) = Inr (eval t1) type1
eval (CaseInl t1 varName t2) = 
  let t1_eval = eval t1 in
    if t1_eval == t1
      then case t1_eval of (Inl inl_eval inl_type) -> substitute varName inl_eval t2
                           _                       -> ErrorT
      else eval (CaseInl (eval t1) varName t2)
eval (CaseInr t1 varName t2) = 
  let t1_eval = eval t1 in
    if t1_eval == t1
      then case t1_eval of (Inr inr_eval inr_type) -> substitute varName inr_eval t2
                           _                       -> ErrorT
      else eval (CaseInr (eval t1) varName t2)
eval t = t

eval_to_value::Term->Value
eval_to_value t =
  let evaled_t = eval t in
    case evaled_t of (Abs var type1 term) -> Lambda (var, type1, term)
                     TrueT -> TrueValue
                     FalseT -> FalseValue
                     Var _ -> ErrorValue
                     term -> ValueTerm term

typeCheck::Term->Context->Type
typeCheck TrueT _  = TBool
typeCheck FalseT _ = TBool
typeCheck (Var var) ctx = getVarType var ctx
typeCheck (Inl t1 type1) ctx = case type1 of TSum lhs rhs -> if lhs == (typeCheck t1 ctx) then type1 else TUnknown 
typeCheck (Inr t1 type1) ctx = case type1 of TSum lhs rhs -> if rhs == (typeCheck t1 ctx) then type1 else TUnknown
typeCheck (CaseInl t1 var t2) ctx = 
  let t1_type = typeCheck t1 ctx in
    case t1_type of (TSum type1 type2) -> typeCheck t2 ((var, type1):ctx)
                    _                  -> TUnknown 
typeCheck (CaseInr t1 var t2) ctx = 
  let t1_type = typeCheck t1 ctx in
    case t1_type of (TSum type1 type2) -> typeCheck t2 ((var, type2):ctx)
                    _                  -> TUnknown 
typeCheck (Abs var type1 term) ctx = 
  let bodyType = typeCheck term ((var, type1):ctx) in
    TFun type1 bodyType
typeCheck (App t1 t2) ctx = 
  let t1_type = typeCheck t1 ctx in
    let t2_type = typeCheck t2 ctx in
      case t1_type of (TFun t1_type1 t1_type2) -> if t2_type == t1_type1 then t1_type2 else TUnknown
                      _                        -> TUnknown
  
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
  prompt ((\t -> typeCheck t []) . (\t -> let (term, _) = uniquify t [] 0 in term)) (eval_to_value . (\t -> let (term, _) = uniquify t [] 0 in term))   
