module Main where

import System.IO
import Data.List

type Variable = String
type Label = String
type VarList = [(Variable, Int)]
type Context = [(Variable, Type)]
type Subtypes = [(Type, Type)]
type VariantTags = [(Label,Type)]

data Value = Lambda (Variable, Type, Term) | TrueValue | FalseValue | ErrorValue | ValueTerm Term deriving Show
data Type = TFun Type Type | TVariant VariantTags | TBool | TTop | TUnknown deriving (Show, Read, Eq)
data Term = Var Variable | Abs Variable Type Term | App Term Term | Tag Label Term | Case Term [(Label, Variable, Term)] | TrueT | FalseT | ErrorT deriving (Show, Read, Eq)

isVarWidthSubtype::VariantTags->VariantTags->Bool
isVarWidthSubtype [] _ = True
isVarWidthSubtype ((label1, type1):tags1) [] = False
isVarWidthSubtype ((label1, type1):tags1) ((label2, type2):tags2) =
  if (label1 == label2) && (type1 == type2) then isVarWidthSubtype tags1 tags2 else False 

isVarDepthSubtype::VariantTags->VariantTags->Subtypes->Bool
isVarDepthSubtype ((label1, type1):tags1) ((label2, type2):tags2) subtypes =
  if (label1 == label2) && (isSubtype type1 type2 subtypes subtypes) 
    then isVarDepthSubtype tags1 tags2 subtypes 
    else False
isVarDepthSubtype _ _ _ = False

isVarPermSubtype::VariantTags->Int->VariantTags->Bool
isVarPermSubtype [] tagsComplete tags2 = 
  if (tagsComplete) == (length tags2) then True else False
isVarPermSubtype ((toGoLabel1, toGoType):tagsToGo1) tagsComplete tags2 =
  let result = lookup toGoLabel1 tags2 in
    case result of Just type2 -> if (toGoType == type2) then isVarPermSubtype tagsToGo1 (tagsComplete+1) tags2 else False
                   _          -> False  


isSubtype::Type->Type->Subtypes->Subtypes->Bool
isSubtype type1 TTop _ _ = True
isSubtype (TFun funType1_1 funType1_2) (TFun funType2_1 funType2_2) subs origSubtypes = 
  (isSubtype funType2_1 funType1_1 subs origSubtypes) && (isSubtype funType1_2 funType2_2 subs origSubtypes)  
isSubtype (TVariant tvar1) (TVariant tvar2) subs origSubtypes =
  (isVarWidthSubtype tvar1 tvar2) || (isVarDepthSubtype tvar1 tvar2 origSubtypes) || (isVarPermSubtype tvar1 0 tvar2) 
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
               t -> (t, lambdaId)
               
substitute::Variable->Term->Term->Term
substitute varName replaceTerm term = 
  case term of Var var          -> if var==varName then replaceTerm else term 
               Abs var type1 t2 -> Abs var type1 (substitute varName replaceTerm t2)
               App t1 t2        -> App (substitute varName replaceTerm t1) (substitute varName replaceTerm t2)

substituteLabel::[(Label, Variable, Term)]->Label->Term->Term
substituteLabel [] _ t1 = ErrorT
substituteLabel ((case_label, case_var, case_term):labels) matchLabel replaceValue = if case_label == matchLabel 
                                                                                       then substitute case_var replaceValue case_term 
                                                                                       else substituteLabel labels matchLabel replaceValue 

typeCheckVariantCase::(Label, Variable, Term)->[(Label, Type)]->Context->Type
typeCheckVariantCase (case_label, case_var, case_term) variantTypeList ctx = 
  let result = lookup case_label variantTypeList in 
    case result of Just result_type -> typeCheck case_term ((case_var, result_type):ctx)
                   _                -> TUnknown    

typeCheckListMustMatch::[Type]->Type
typeCheckListMustMatch [] = TUnknown
typeCheckListMustMatch (type1:types) = if (all (\x -> x == type1) types) then type1 else TUnknown  

eval::Term->Term
eval (App (Abs var type1 t1) t2) = 
  let t2_eval = eval t2 in
    if t2_eval == t2 
      then eval (substitute var t2_eval t1) 
      else eval (App (Abs var type1 t1) (eval t2))
eval (App t1 t2) = eval (App (eval t1) t2)
eval (Tag label1 t1) = Tag label1 (eval t1)
eval (Case t1 patterns) = 
  let t1_eval = eval t1 in
    if t1_eval == t1
      then case t1_eval of (Tag tag_label tag_eval) -> substituteLabel patterns tag_label tag_eval 
                           _                        -> ErrorT
      else eval (Case (eval t1) patterns)
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
typeCheck (Tag label1 t1) ctx = TVariant [(label1, typeCheck t1 ctx)]
typeCheck (Case t1 cases) ctx = 
  let t1_type = typeCheck t1 ctx in
    case t1_type of (TVariant variantList) -> let typeList = map (\x->typeCheckVariantCase x variantList ctx) cases in typeCheckListMustMatch typeList
                    _                     -> TUnknown 
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
