module Main where

import System.IO
import Data.List

type Variable = String
type Location = Int
type VarList = [(Variable, Int)]
type Context = [(Variable, Type)] -- Gamma
type StoreVals = [(Location, Term)] -- Mu
type StoreTypes = [(Location, Type)] -- Sigma 

data Value = LambdaValue (Variable, Type, Term) | LocationValue Location | TrueValue | FalseValue | UnitValue | ErrorValue | ValueTerm Term deriving Show
data Type = TFun Type Type | TRef Type | TBool | TUnit | TUnknown deriving (Show, Read, Eq)
data Term = Var Variable | Abs Variable Type Term | App Term Term | Seq Term Term | Ref Term | Deref Term | Assign Term Term | Loc Location | TrueT | FalseT | ErrorT | UnitT deriving (Show, Read, Eq)

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
                          Nothing -> name ++ (show 0)

uniquify_and_derive::Term->VarList->Int->(Term, Int)
uniquify_and_derive term vars lambdaId = 
  case term of Var var    -> (Var (getVarName var vars), lambdaId)
               Abs var type1 t2 -> 
                 let newLambdaId1 = lambdaId + 1 in 
                   let newVars = (var, lambdaId):vars in
                     let (uniqueBody, newLambdaId2) = uniquify_and_derive t2 newVars newLambdaId1 in 
                       (Abs (getVarName var newVars) type1 uniqueBody, newLambdaId2)
               App t1 t2 ->
                 let (uniqueT1, newLambdaId1) = uniquify_and_derive t1 vars lambdaId in
                   let (uniqueT2, newLambdaId2) = uniquify_and_derive t2 vars newLambdaId1 in
                     (App uniqueT1 uniqueT2, newLambdaId2)
               Seq t1 t2->
                 let (uniqueT1, newLambdaId1) = uniquify_and_derive t1 vars lambdaId in
                   let (uniqueT2, newLambdaId2) = uniquify_and_derive t2 vars newLambdaId1 in
                     let newLambdaId3 = newLambdaId2 + 1 in
                       (App (Abs ("x" ++ (show newLambdaId3)) TUnit uniqueT2) uniqueT1, newLambdaId3)                 
               t -> (t, lambdaId)
               
substitute::Variable->Term->Term->Term
substitute varName replaceTerm term = 
  case term of Var var          -> if var==varName then replaceTerm else term 
               Abs var type1 t2 -> Abs var type1 (substitute varName replaceTerm t2)
               App t1 t2        -> App (substitute varName replaceTerm t1) (substitute varName replaceTerm t2)
               t                -> t

add_loc_val::a->[(Location, a)]->(Location, [(Location, a)])
add_loc_val val mu = 
  let new_loc = length mu in
    (new_loc, (new_loc, val):mu)
    
get_loc_val::Location->[(Location, a)]->Maybe a
get_loc_val loc [] = Nothing
get_loc_val loc ((currLoc, currVal):muRest) = 
  if (loc == currLoc) then Just currVal else get_loc_val loc muRest

set_loc_val::Location->a->[(Location, a)]->[(Location, a)]->[(Location, a)]
set_loc_val loc val prevVals [] = prevVals
set_loc_val loc val prevVals ((currLoc, currVal):muRest) = 
  if loc == currLoc 
    then prevVals ++ ((currLoc, val) : muRest) 
    else set_loc_val loc val ((currLoc, currVal) : prevVals) muRest

eval::Term -> StoreVals -> (Term, StoreVals)
eval (App (Abs var type1 t1) t2) mu = 
  let (t2_eval, t2_mu) = eval t2 mu in
    if t2_eval == t2 
      then eval (substitute var t2_eval t1) t2_mu 
      else eval (App (Abs var type1 t1) t2_eval) t2_mu
eval (App t1 t2) mu = 
  let (t1_eval, t1_mu) = eval t1 mu in eval (App t1_eval t2) t1_mu
eval (Ref t1) mu = 
  let (t1_eval, t1_mu) = eval t1 mu in 
    let (new_loc, new_mu) = add_loc_val t1_eval t1_mu in
      (Loc new_loc, new_mu) 
eval (Deref t1) mu = 
  let (t1_eval, t1_mu) = eval t1 mu in
    case t1_eval of Loc loc -> let result = get_loc_val loc t1_mu in case result of Just res -> (res, t1_mu); Nothing -> (ErrorT, t1_mu)

eval (Assign t1 t2) mu = 
  let (t1_eval, t1_mu) = eval t1 mu in
    let (t2_eval, t2_mu) = eval t2 t1_mu in
      case t1_eval of Loc loc -> (UnitT, set_loc_val loc t2_eval [] t2_mu)
eval t mu = (t, mu)

eval_to_value::Term->StoreVals->Value
eval_to_value t mu =
  let (evaled_t, _) = eval t mu in
    case evaled_t of (Abs var type1 term) -> LambdaValue (var, type1, term)
                     Loc loc -> LocationValue loc
                     TrueT -> TrueValue
                     FalseT -> FalseValue
                     UnitT -> UnitValue
                     Var _ -> ErrorValue
                     term -> ValueTerm term

typeCheck::Term->Context->StoreTypes->(Type, StoreTypes)
typeCheck TrueT _ sigma = (TBool, sigma)
typeCheck FalseT _ sigma = (TBool, sigma)
typeCheck UnitT _ sigma = (TUnit, sigma)
typeCheck (Var var) cxt sigma = (getVarType var cxt, sigma)
typeCheck (Abs var type1 term) cxt sigma = 
  let (bodyType, body_sigma) = typeCheck term ((var, type1):cxt) sigma in
    (TFun type1 bodyType, body_sigma)
typeCheck (App t1 t2) ctx sigma = 
  let (t1_type, t1_sigma) = typeCheck t1 ctx sigma in
    let (t2_type, t2_sigma) = typeCheck t2 ctx t1_sigma in
      case t1_type of (TFun t1_type1 t1_type2) -> if t2_type == t1_type1 then (t1_type2, t2_sigma) else (TUnknown, t2_sigma)
                      _                        -> (TUnknown, t2_sigma)
typeCheck (Ref t1) ctx sigma = 
  let (t1_type, t1_sigma) = typeCheck t1 ctx sigma in
    let (new_loc, new_sigma) = add_loc_val t1_type sigma in 
      (TRef t1_type, new_sigma)
typeCheck (Loc loc) ctx sigma = 
  let result = get_loc_val loc sigma in case result of Just t  -> (TRef t, sigma)
                                                       Nothing -> (TUnknown, sigma)
typeCheck (Deref t1) ctx sigma =
  let (t1_type, t1_sigma) = typeCheck t1 ctx sigma in
    case t1_type of TRef type1 -> (type1, t1_sigma) 
                    _          -> (TUnknown, t1_sigma)
typeCheck (Assign t1 t2) ctx sigma = 
  let (t1_type, t1_sigma) = typeCheck t1 ctx sigma in
    let (t2_type, t2_sigma) = typeCheck t2 ctx t1_sigma in
      case t1_type of TRef type1 -> if type1 == t2_type then (TUnit, t2_sigma) else (TUnknown, t2_sigma)
                      _          -> (TUnknown, t1_sigma) 

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
  prompt ((\t -> typeCheck t [("unit", TUnit)] []) . (\t -> let (term, _) = uniquify_and_derive t [] 0 in term)) ((\t -> eval_to_value t []) . (\t -> let (term, _) = uniquify_and_derive t [] 0 in term))   
