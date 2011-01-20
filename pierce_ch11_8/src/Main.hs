module Main where

import System.IO
import Data.List

type Variable = String
type VarList = [(Variable, Int)]
type Context = [(Variable, Type)]

data Pattern = PVar Variable | PRecord [(String, Pattern)] deriving (Eq, Show, Read)
data Value = Lambda (Variable, Type, Term) | RecordValue [(String, Value)] | TrueValue | FalseValue | ErrorValue | ValueTerm Term deriving Show
data Type = TFun Type Type | TRecord [(String, Type)] | TBool | TUnknown deriving (Show, Read, Eq)
data Term = Var Variable | Abs Variable Type Term | App Term Term | Let Variable Term Term | LetP Pattern Term Term | Record [(String, Term)] | Projection String Term | TrueT | FalseT | ErrorT deriving (Show, Read, Eq)

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

match::Pattern->Term->Term->Term 
match (PVar pvar) matchTerm substTarget = substitute pvar matchTerm substTarget
match (PRecord prec) (Record termRec) substTarget = 
  let f currentSubst (precLabel, precPattern) = case (lookup precLabel termRec) of Just resultTerm -> match precPattern resultTerm currentSubst
                                                                                   _               -> ErrorT 
  in
    foldl f substTarget prec  

buildMatchCtx::Pattern->Term->Maybe Context->Maybe Context
buildMatchCtx pat t1 ctx = 
  case pat of PVar pvar    -> case ctx of Just realCtx -> Just ((pvar, typeCheck t1 realCtx):realCtx)
                                          Nothing      -> Nothing
              PRecord prec -> case t1 of Record ts -> let 
                                                        patCtxMaker newCtx (patName, patPattern) = 
                                                          case lookup patName ts of Just resultTerm -> buildMatchCtx patPattern resultTerm newCtx
                                                                                    _               -> Nothing
                                                      in foldl patCtxMaker ctx prec
                                         _         -> Nothing

uniquifyPattern::Pattern->VarList->Int->(Pattern, VarList, Int)
uniquifyPattern pat vars lambdaId = 
  case pat of PVar pvar    -> 
                let newLambdaId = lambdaId + 1 in
                  let newName = pvar ++ (show (newLambdaId)) in 
                    (PVar newName, (pvar, newLambdaId):vars, newLambdaId)
              PRecord prec -> 
                let (patList, newVars, newLambdaId) = foldl helper ([], vars, lambdaId) prec in 
                  (PRecord patList, newVars, newLambdaId) where 
                    helper (pats, currentVars, currentLambdaId) (patName, patTerm) = 
                      let (uniquePat, uniqueVarList, uniqueLambdaId) = uniquifyPattern patTerm currentVars currentLambdaId in 
                        ((patName, uniquePat):pats, uniqueVarList, uniqueLambdaId)
                      
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
               Let var t1 t2 -> 
                 let newLambdaId1 = lambdaId + 1 in 
                   let newVars = (var, lambdaId):vars in
                     let (uniqueT1, newLambdaId2) = uniquify t1 newVars newLambdaId1 in
                       let (uniqueT2, newLambdaId3) = uniquify t2 newVars newLambdaId2 in
                         (Let (getVarName var newVars) uniqueT1 uniqueT2, newLambdaId3)
               LetP pat t1 t2 -> 
                 let newLambdaId1 = lambdaId + 1 in 
                   let (newPat, newVars, newLambdaId1) = uniquifyPattern pat vars lambdaId in
                     let (uniqueT1, newLambdaId2) = uniquify t1 vars newLambdaId1 in
                       let (uniqueT2, newLambdaId3) = uniquify t2 newVars newLambdaId2 in
                         (LetP newPat uniqueT1 uniqueT2, newLambdaId3)
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
               Let var t1 t2    -> Let var (substitute varName replaceTerm t1) (substitute varName replaceTerm t2)
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
eval (Let var t1 t2) = 
  let t1_eval = eval t1 in
    if t1_eval == t1
      then eval (substitute var t1_eval t2)
      else eval (Let var t1_eval t2) 
eval (LetP pat t1 t2) = 
  let t1_eval = eval t1 in
    if t1_eval == t1
      then eval (match pat t1_eval t2)
      else eval (LetP pat t1_eval t2) 
eval t = t

eval_to_value::Term->Value
eval_to_value t =
  let evaled_t = eval t in
    case evaled_t of (Abs var type1 term) -> Lambda (var, type1, term)
                     TrueT      -> TrueValue
                     FalseT     -> FalseValue
                     Var _      -> ErrorValue
                     Record ts  -> RecordValue (map (\(labelName, t)->(labelName, eval_to_value t)) ts)  
                     term       -> ValueTerm term

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
typeCheck (Let var t1 t2) ctx = 
  let t1_type = typeCheck t1 ctx in
    typeCheck t2 ((var, t1_type):ctx)

typeCheck (LetP pat t1 t2) ctx =
  let new_context = buildMatchCtx pat t1 (Just ctx) in
    case new_context of Just newCtx -> typeCheck t2 newCtx
                        Nothing     -> TUnknown 
  
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
    (putStrLn . show . (\t -> let (term, _) = uniquify t [] 0 in term) . read) input
    (putStrLn . show . action . read) input
    (putStrLn . show . action2 . read) input
    prompt action action2
    
main::IO()
main = 
  prompt ((\t -> typeCheck t []) . (\t -> let (term, _) = uniquify t [] 0 in term)) (eval_to_value . (\t -> let (term, _) = uniquify t [] 0 in term))   
