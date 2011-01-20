module Main where

import System.IO
import Data.List

type Variable = String
type VarList = [(Variable, Int)]
type Context = [(Variable, Type)]
type Subtypes = [(Type, Type)]
type Fields = [(String, Type)]

data Value = Lambda (Variable, Type, Term) | RecordValue [(String, Value)] | TrueValue | FalseValue | ErrorValue | ValueTerm Term deriving Show
data Type = TFun Type Type | TRecord Fields | TBool | TTop | TUnknown deriving (Show, Read, Eq)
data Term = Record [(String, Term)] | Projection String Term |Var Variable | Abs Variable Type Term | App Term Term | TrueT | FalseT | ErrorT deriving (Show, Read, Eq)


isRcdWidthSubtype::Fields->Fields->Bool
isRcdWidthSubtype [] [] = True
isRcdWidthSubtype ((label1, type1):fields1) [] = True
isRcdWidthSubtype ((label1, type1):fields1) ((label2, type2):fields2) = 
  if (label1 == label2) && (type1 == type2) 
    then isRcdWidthSubtype fields1 fields2 
    else False
isRcdWidthSubtype _ _ = False 

isRcdDepthSubtype::Fields->Fields->Subtypes->Bool
isRcdDepthSubtype [] [] _ = True
isRcdDepthSubtype ((label1, type1):fields1) ((label2, type2):fields2) subtypes = 
  if (label1 == label2) && (isSubtype type1 type2 subtypes subtypes) 
    then isRcdDepthSubtype fields1 fields2 subtypes
    else False
isRcdDepthSubtype _ _ _ = False 

isRcdPermSubtype::Fields->Int->Fields->Bool
isRcdPermSubtype [] fieldsComplete fields2 = 
  if (fieldsComplete) == (length fields2) then True else False
isRcdPermSubtype ((toGoLabel1, toGoType):fieldsToGo1) fieldsComplete fields2 =
  let result = lookup toGoLabel1 fields2 in
    case result of Just type2 -> if (toGoType == type2) then isRcdPermSubtype fieldsToGo1 (fieldsComplete+1) fields2 else False
                   _          -> False  

isSubtype::Type->Type->Subtypes->Subtypes->Bool
isSubtype type1 TTop _ _ = True
isSubtype (TFun funType1_1 funType1_2) (TFun funType2_1 funType2_2) subs origSubtypes = 
  (isSubtype funType2_1 funType1_1 subs origSubtypes) && (isSubtype funType1_2 funType2_2 subs origSubtypes)  
isSubtype (TRecord trec1) (TRecord trec2) subs origSubtypes = 
  (isRcdWidthSubtype trec1 trec2) || (isRcdDepthSubtype trec1 trec2 origSubtypes) || (isRcdPermSubtype trec1 0 trec2) 
isSubtype type1 type2 _ _ | type1 == type2 = True
isSubtype type1 type2 [] _ = False
isSubtype type1 type2 ((subType1, subType2):subtypes) origSubtypes = 
  if type1 == subType1 
    then (type2 == subType2) || (isSubtype subType2 type2 origSubtypes origSubtypes) || (isSubtype type1 type2 subtypes origSubtypes)
    else isSubtype type1 type2 subtypes origSubtypes
    
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
               Record ts -> 
                 let f (tList, currentId) (labelName, term) = (let (newTerm, newInt) = uniquify term vars currentId in (tList ++ [(labelName, newTerm)], newInt)) in
                   let (uniqueTS, newLambdaId) = foldl f ([], lambdaId) ts in
                     (Record uniqueTS, newLambdaId)
               Projection string term -> 
                 let (uniqueTerm, newLambdaId) = uniquify term vars lambdaId in
                   (Projection string uniqueTerm, newLambdaId)
               t -> (t, lambdaId)
               
substitute::Variable->Term->Term->Term
substitute varName replaceTerm term = 
  case term of Var var          -> if var==varName then replaceTerm else term 
               Abs var type1 t2 -> Abs var type1 (substitute varName replaceTerm t2)
               App t1 t2        -> App (substitute varName replaceTerm t1) (substitute varName replaceTerm t2)
               Record ts        -> Record (map (\(name, t)->(name, substitute varName replaceTerm t)) ts)
               Projection int t -> Projection int (substitute varName replaceTerm t)
               t                -> t

eval::Term->Term
eval (App (Abs var type1 t1) t2) = 
  let t2_eval = eval t2 in
    if t2_eval == t2 
      then eval (substitute var t2_eval t1) 
      else eval (App (Abs var type1 t1) (eval t2))
eval (App t1 t2) = eval (App (eval t1) t2)
eval (Projection labelName t1) = 
  let t1_eval = eval t1 in
    if t1_eval == t1 
      then case t1_eval of Record ts -> 
                             let result = lookup labelName ts in
                               case result of Just value -> value
                                              _ -> ErrorT
                           _ -> ErrorT
      else eval (Projection labelName t1_eval)
eval (Record ts) =
  Record (map (\(labelName, t)->(labelName, eval t)) ts)
eval t = t

eval_to_value::Term->Value
eval_to_value t =
  let evaled_t = eval t in
    case evaled_t of (Abs var type1 term) -> Lambda (var, type1, term)
                     TrueT -> TrueValue
                     FalseT -> FalseValue
                     Var _ -> ErrorValue
                     Record ts  -> RecordValue (map (\(labelName, t)->(labelName, eval_to_value t)) ts)  
                     term -> ValueTerm term

typeCheck::Term->Context->Type
typeCheck TrueT _  = TBool
typeCheck FalseT _ = TBool
typeCheck (Var var) ctx = getVarType var ctx
typeCheck (Record ts) ctx = TRecord (map (\(labelName, term)->(labelName, typeCheck term ctx)) ts)
typeCheck (Projection labelName t1) ctx = 
  let t1_type = typeCheck t1 ctx in
    case t1_type of TRecord record -> 
                      let result = lookup labelName record in 
                        case result of Just fieldType -> fieldType
                                       _              -> TUnknown
                    _ -> TUnknown
typeCheck (Abs var type1 term) ctx = 
  let bodyType = typeCheck term ((var, type1):ctx) in
    TFun type1 bodyType
typeCheck (App t1 t2) ctx = 
  let t1_type = typeCheck t1 ctx in
    let t2_type = typeCheck t2 ctx in
      case t1_type of (TFun t1_type1 t1_type2) -> if isSubtype t2_type t1_type1 [] [] then t1_type2 else TUnknown
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
