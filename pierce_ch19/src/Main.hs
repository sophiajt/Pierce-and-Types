module Main where

import System.IO
import Data.List

type ClassName = String
type Variable = String
type MethodName = String
type FieldName = String

type VarDecl = (ClassName, Variable)
type Field = VarDecl
type Param = VarDecl

type Context = [(Variable, Type)]
type ClassContext = [(ClassName, Class)]
type VarList = [(Variable, Int)]

type Method = (ClassName, MethodName, [Param], Term)
type Class = (ClassName, ClassName, [Field], [(MethodName, Method)])

data Term = Seq Term Term | ClassDecl Class | Var Variable | TrueT | FalseT | FieldAccess Term FieldName | MethodInvoke Term MethodName [Term] | New ClassName [Term] | Cast ClassName Term | UnitT | ErrorT deriving (Show, Read)
data Type = TObject | TFun [Type] Type | TClass ClassName | TUnit | TError String deriving (Eq, Show)

fields::ClassName->ClassContext->[Field]
fields name mappings =
  let result = lookup name mappings in
    case result of Just (_, "Object", clsFields, _) -> clsFields
                   Just (_, parent, clsFields, _) -> fields parent mappings ++ clsFields
                   _ -> []  

getVarName::Variable->VarList->Variable
getVarName name vars = 
  let f (vname, _) = (vname == name) in 
    let valueFound = find f vars in
       case valueFound of Just (name, id) -> name ++ (show id) 
                          Nothing -> name

uniquifyFields::[Field]->VarList->Int->([Field], VarList)
uniquifyFields [] vars lambdaId = ([], vars)
uniquifyFields ((fieldClass, fieldName):fields) vars lambdaId = 
  let newVars = vars ++ [(fieldName, lambdaId)] in
    let (nextFields, nextVars) = uniquifyFields fields newVars lambdaId in
      let newFieldName = getVarName fieldName newVars in
        ((fieldClass, newFieldName):nextFields, nextVars)  

uniquifyMethods::[(MethodName, Method)]->VarList->Int->([(MethodName, Method)], Int)
uniquifyMethods [] vars lambdaId = ([], lambdaId)
uniquifyMethods ((methodName, methodDef):methods) vars lambdaId =
  let (methClassName, methMethodName, methParams, methReturnTerm) = methodDef in
    let (newMethodParams, newVars) = uniquifyFields methParams vars lambdaId in
      let (newReturnTerm, _, newLambdaId1) = uniquify methReturnTerm newVars lambdaId in
        let (newMethods, newLambdaId2) = uniquifyMethods methods newVars newLambdaId1 in
          ((methodName, (methClassName, methMethodName, newMethodParams, newReturnTerm)):newMethods, newLambdaId2) 


thd4::((a, b, c, d)->c)
thd4 (_, _, t, _) = t

fth4::((a, b, c, d)->d)
fth4 (_, _, _, t) = t

mapcarry::((a,b)->(a,b))->[a]->b->([a],b)
mapcarry f [] b = ([], b)
mapcarry f (a:as) b =
  let (result_a, result_b) = f (a,b) in
    let (follow_as, follow_b) = mapcarry f as result_b in
      (result_a:follow_as, follow_b)

uniquify::Term->VarList->Int->(Term, VarList, Int)
uniquify term vars lambdaId = 
  case term of Seq t1 t2 ->
                 let (unique_t1, newVarList1, newLambdaId) = uniquify t1 vars lambdaId in
                   let (unique_t2, newVarList2, newLambdaId2) = uniquify t2 newVarList1 newLambdaId in
                     (Seq unique_t1 unique_t2, newVarList2, newLambdaId2)
               ClassDecl (clsName, parentName, fields, methods) ->
                 let newLambdaId1 = lambdaId + 1 in
                   let (newFields, newVarList1) = uniquifyFields fields vars newLambdaId1 in
                     let (newMethods, newLambdaId2) = uniquifyMethods methods vars newLambdaId1 in
                       (ClassDecl (clsName, parentName, newFields, newMethods), newVarList1, newLambdaId2)
               Var var -> (Var (getVarName var vars), vars, lambdaId)
               FieldAccess t1 fieldName -> 
                 let newFieldName = getVarName fieldName vars in
                   let (uniqueTerm, newVarList, newLambdaId) = uniquify t1 vars lambdaId in 
                     (FieldAccess uniqueTerm newFieldName, newVarList, newLambdaId) 
               MethodInvoke t1 methodName argTerms ->
                 let (unique_t1, newVarList, newLambdaId) = uniquify t1 vars lambdaId in
                   let methodUniq (term1, lambdaId1) = (let (u1, _, u2) = uniquify term1 newVarList lambdaId1 in (u1, u2)) in 
                     let (newArgs, newLambdaId2) = mapcarry methodUniq argTerms lambdaId in
                       (MethodInvoke unique_t1 methodName newArgs, newVarList, newLambdaId2) 
               New className terms ->
                 let methodUniq (term1, lambdaId1) = (let (u1, _, u2) = uniquify term1 vars lambdaId1 in (u1, u2)) in 
                   let (unique_terms, newLambdaId2) = mapcarry methodUniq terms lambdaId in
                     (New className unique_terms, vars, newLambdaId2) 
               Cast className term -> 
                 let (unique_term, newVarList, newLambdaId) = uniquify unique_term vars lambdaId in
                   (Cast className unique_term, newVarList, newLambdaId)
                   
               t -> (t, vars, lambdaId)


substitute::Variable->Term->Term->Term
substitute varName replaceTerm term = 
  case term of ClassDecl (clsName, parentName, fields, methods) -> 
                 let new_methods = map (\(methName, (methClassName, methodName, methParams, methTerm)) -> (methName, (methClassName, methodName, methParams, substitute varName replaceTerm methTerm)) ) methods in 
                   ClassDecl (clsName, parentName, fields, new_methods) 
               Var var -> if var == varName then replaceTerm else term
               FieldAccess t1 fieldName -> FieldAccess (substitute varName replaceTerm t1) fieldName
               MethodInvoke t1 methodName argTerms -> 
                 let t1_subst = substitute varName replaceTerm t1 in
                   let argTerms_subst = map (\t->substitute varName replaceTerm t) argTerms in
                     MethodInvoke t1_subst methodName argTerms_subst
               New className terms -> 
                 let terms_subst = map (\t->substitute varName replaceTerm t) terms in
                   New className terms_subst
               Seq t1 t2 ->
                 let t1_subst = substitute varName replaceTerm t1 in
                   let t2_subst = substitute varName replaceTerm t2 in
                     Seq t1_subst t2_subst
               Cast className term -> substitute varName replaceTerm term
               TrueT -> TrueT
               FalseT -> FalseT
               ErrorT -> ErrorT
               UnitT -> UnitT

lookup2:: (Eq b) => b -> [(a,b)] -> Maybe a
lookup2 _key []          =  Nothing
lookup2  key ((x,y):xys)
    | key == y          =  Just x
    | otherwise         =  lookup2 key xys

isSubtype::Type->Type->ClassContext->Bool
isSubtype _ (TClass "Object") _ = True
isSubtype (TClass "Object") _ _ = False
isSubtype (TClass x) (TClass y) clsDefs = 
  if x == y 
    then True 
    else let result = lookup x clsDefs in
      case result of Just (foundClsName, foundParentName, _, _) -> (foundParentName == y) || (isSubtype (TClass foundParentName) (TClass y) clsDefs) 
                     _ -> False
isSubtype _ _ _ = False
                   
typecheck::Term->ClassContext->Context->(Type, ClassContext, Context)
typecheck (Var v) clsDefs ctx = 
  let result = lookup v ctx in
    case result of Just t  -> (t, clsDefs, ctx)
                   Nothing -> (TError "Can't find var", clsDefs, ctx)
typecheck (FieldAccess t1 fieldName) clsDefs ctx =
  let (t1_typecheck, t1_clsDefs, t1_ctx) = typecheck t1 clsDefs ctx in
    case t1_typecheck of 
      TClass clsName ->  let clsDefResult = lookup clsName clsDefs in
        case clsDefResult of 
          Just clsDef -> let fieldResult = lookup2 fieldName (fields clsName clsDefs) in
            case fieldResult of
              Just fieldClass -> (TClass fieldClass, clsDefs, ctx)
              _ -> (TError "Can't find field for field access", t1_clsDefs, t1_ctx)
          _ -> (TError "Can't find class for field access" , t1_clsDefs, t1_ctx)
      TError terror -> (t1_typecheck, t1_clsDefs, t1_ctx)
      _ -> (TError "Field access of non-object", t1_clsDefs, t1_ctx) 
typecheck (MethodInvoke t1 methodName argTerms) clsDefs ctx = 
  let (t1_typecheck, t1_clsDefs, t1_ctx) = typecheck t1 clsDefs ctx in
    case t1_typecheck of 
      TClass clsName -> (mtypecheck clsName methodName argTerms t1_clsDefs t1_ctx, t1_clsDefs, t1_ctx)  
      _ -> (TError "Can't find class for method access", t1_clsDefs, t1_ctx)
typecheck (New clsName terms) clsDefs ctx = 
  let result = lookup clsName clsDefs in
    case result of 
      Just (_, _, _, _) -> let newFieldCtx = mparamsContext terms (fields clsName clsDefs) clsDefs ctx in
        case newFieldCtx of 
          Just newParamsCtx -> (TClass clsName, clsDefs, newParamsCtx) 
          _ -> (TError "New context creation error", clsDefs, ctx)
      _ -> (TError "Can't find class in new expression", clsDefs, ctx)
typecheck (Cast clsName term) clsDefs ctx =
  let (term_type, term_clsDefs, term_ctx) = typecheck term clsDefs ctx in
    case term_type of 
      (TClass term_typename) -> if (isSubtype term_type (TClass clsName) clsDefs) 
                                  then (TClass clsName, term_clsDefs, term_ctx)
                                  else if (isSubtype (TClass clsName) term_type clsDefs) && (TClass clsName /= term_type) 
                                    then (TClass clsName, term_clsDefs, term_ctx)
                                    else (TError "Improper subtypes in cast", term_clsDefs, term_ctx)
typecheck (ClassDecl (clsName, parentName, fields, methods)) clsDefs ctx =
  let new_clsDefs = (clsName, (clsName, parentName, fields, methods)):clsDefs in
    let method_checks = map (\m -> isMethodOverridingCorrectly clsName m new_clsDefs ctx) methods in
      let method_checks_all = and method_checks in
        if method_checks_all 
          then (TClass clsName, new_clsDefs, ctx)
          else (TError "Incorrect method override", new_clsDefs, ctx)
          
typecheck (Seq t1 t2) clsDefs ctx = 
  let (t1_type, t1_clsDefs, t1_ctx) = typecheck t1 clsDefs ctx in
    case t1_type of TError terror -> (TError terror, clsDefs, ctx)
                    _ -> typecheck t2 t1_clsDefs t1_ctx
typecheck UnitT clsDefs ctx = (TUnit, clsDefs, ctx)
typecheck FalseT clsDefs ctx = (TClass "Bool", clsDefs, ctx)
typecheck TrueT clsDefs ctx = (TClass "Bool", clsDefs, ctx)

mparamsContext::[Term]->[Param]->ClassContext->Context->Maybe Context
mparamsContext [] [] _ ctx = Just ctx 
mparamsContext [] _ _ _ = Nothing
mparamsContext _ [] _ _ = Nothing
mparamsContext (t:ts) (p:ps) clsDefs ctx = 
  let (t_type, t_clsDefs, t_ctx) = typecheck t clsDefs ctx in
    if isSubtype t_type (TClass (fst p)) t_clsDefs 
      then mparamsContext ts ps t_clsDefs ((snd p, t_type):t_ctx)
      else Nothing

mtype::ClassName->MethodName->ClassContext->Context->Type
mtype className methodName clsDefs ctx = 
  case lookup className clsDefs of 
    Just (_, parent, _, methods) -> case lookup methodName methods of 
                                      Just (_, _, params, returnTerm) -> TFun (map (\(t, _)->TClass t) params) (let (type1, newClsDefs, newCtx) = typecheck returnTerm clsDefs (("this", TClass className):ctx) in type1)
                                      _ -> mtype parent methodName clsDefs ctx 
    _ -> TError "Can't find class definition in method type"

isMethodOverridingCorrectly::ClassName->(MethodName, Method)->ClassContext->Context->Bool
isMethodOverridingCorrectly className (methName, methDef) clsDefs ctx =
  case lookup className clsDefs of
    Just (_, parent, _, _) -> let methType = mtype className methName clsDefs ctx in
      override parent methName methType clsDefs ctx
    _ -> False 
    

mtypecheck::ClassName->MethodName->[Term]->ClassContext->Context->Type
mtypecheck className methodName args clsDefs ctx = 
  case lookup className clsDefs of 
    Just (_, parent, _, methods) -> case lookup methodName methods of 
                                      Just (_, _, params, returnTerm) -> let mparamsCtx = mparamsContext args params clsDefs ctx in
                                        case mparamsCtx of 
                                          Just new_ctx -> let (return_type, return_clsDefs, return_ctx) = typecheck returnTerm clsDefs (("this", TClass className):new_ctx) in return_type
                                          _ -> TError "New context can't be created in method typecheck"
                                      _ -> mtypecheck parent methodName args clsDefs ctx 
    _ -> TError "Can't find class definition in method typecheck"
          
mbody::ClassName->MethodName->ClassContext->([Variable], Term)
mbody className methodName mappings = 
  case lookup className mappings of 
    Just (_, parent, _, methods) -> case lookup methodName methods of 
                                      Just (_, _, params, returnTerm) -> (map snd params, returnTerm)   
                                      _ -> mbody parent methodName mappings 
    _ -> ([], ErrorT)

override::ClassName->MethodName->Type->ClassContext->Context->Bool
override className methodName funType clsDefs ctx = 
  let override_type = mtype className methodName clsDefs ctx in
    case override_type of TError _ -> True
                          _ -> if override_type == funType then True else False

getInitField::FieldName->[Field]->[Term]->Maybe Term
getInitField _ [] _ = Nothing
getInitField _ _ [] = Nothing
getInitField fieldName ((fieldClass, fieldDefName):fs) (t:ts) = if fieldName == fieldDefName then Just t else getInitField fieldName fs ts  

invokeMethodBody::[Term]->([Variable], Term)->Term
invokeMethodBody [] (_, term) = term
invokeMethodBody _ ([], term) = term
invokeMethodBody (t:ts) ((v:vs), term) = invokeMethodBody ts (vs, substitute v t term)

eval::Term->ClassContext->(Term, ClassContext)
eval (ClassDecl (clsName, parentName, fields, methods)) clsDefs = (UnitT, (clsName, (clsName, parentName, fields, methods)):clsDefs)  
eval (FieldAccess t1 field) clsDefs =
  let (t1_eval, t1_clsDefs) = eval t1 clsDefs in
    case t1_eval of 
      New clsName terms -> let result = getInitField field (fields clsName clsDefs) terms in case result of Just t  -> eval t t1_clsDefs
                                                                                                            Nothing -> (ErrorT, t1_clsDefs) 
      _ -> (ErrorT, t1_clsDefs)
eval (MethodInvoke t1 methodName argTerms) clsDefs = 
  let (t1_eval, t1_clsDefs) = eval t1 clsDefs in
    case t1_eval of 
      New clsName terms -> (substitute "this" t1_eval (invokeMethodBody terms (mbody clsName methodName clsDefs)), t1_clsDefs)   
      _ -> (ErrorT, t1_clsDefs)   
eval (Cast clsName term) clsDefs = 
  let (term_eval, term_clsDefs) = eval term clsDefs in
    case term_eval of (ClassDecl (termClsName, termParentName, termFields, termMethods)) -> if (isSubtype (TClass termClsName) (TClass clsName) term_clsDefs) then (term_eval, term_clsDefs) else (ErrorT, term_clsDefs)    
eval (New clsName terms) clsDefs = 
  let terms_eval = map (\t -> fst (eval t clsDefs)) terms in
    (New clsName terms_eval, clsDefs)
eval TrueT clsDefs = (TrueT, clsDefs)
eval FalseT clsDefs = (FalseT, clsDefs)
eval (Seq t1 t2) clsDefs = 
  let (t1_eval, t1_clsDefs) = eval t1 clsDefs in
    eval t2 t1_clsDefs
      
eval _ clsDefs = (ErrorT, clsDefs)

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
  prompt ((\t -> typecheck t [("Bool", ("Bool", "Object", [], []))] []) . (\t -> let (term, _, _) = uniquify t [] 0 in term)) ((\e -> eval e []) . (\t -> let (term, _, _) = uniquify t [] 0 in term))   

  
