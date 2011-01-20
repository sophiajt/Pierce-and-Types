module Main where

import System.IO
import Data.List

type Variable = String
type VarList = [(Variable, Int)]
type Lambda = (Variable, Term)

data Term = Var Variable | Abs Variable Term | App Term Term | LambdaValue Lambda deriving (Show, Read)

getVarName::Variable->VarList->Variable
getVarName name vars = 
  let f (vname, _) = (vname == name) in 
    let valueFound = find f vars in
       case valueFound of Just (name, id) -> name ++ (show id) 
                          Nothing -> name

uniquify::Term->VarList->Int->(Term, Int)
uniquify term vars lambdaId = 
  case term of Var var    -> (Var (getVarName var vars), lambdaId)
               Abs var t2 -> 
                 let newLambdaId1 = lambdaId + 1 in 
                   let newVars = (var, lambdaId):vars in
                     let (uniqueBody, newLambdaId2) = uniquify t2 newVars newLambdaId1 in 
                       (Abs (getVarName var newVars) uniqueBody, newLambdaId2)
               App t1 t2 ->
                 let (uniqueT1, newLambdaId1) = uniquify t1 vars lambdaId in
                   let (uniqueT2, newLambdaId2) = uniquify t2 vars newLambdaId1 in
                     (App uniqueT1 uniqueT2, newLambdaId2)
                     
substitute::Variable->Lambda->Term->Term
substitute varName substLambdaValue term = 
  case term of Var var    -> if var==varName then Abs (fst substLambdaValue) (snd substLambdaValue) else term 
               Abs var t2 -> Abs var (substitute varName substLambdaValue t2)
               App t1 t2 -> App (substitute varName substLambdaValue t1) (substitute varName substLambdaValue t2)

eval::Term->Term
eval (App (LambdaValue (var, t1)) (LambdaValue lambda2)) = eval (substitute var lambda2 t1)
eval (App (LambdaValue lambda1) t2) = eval (App (LambdaValue lambda1) (eval t2))
eval (App t1 t2) = eval (App (eval t1) t2)
eval (Abs var term) = LambdaValue (var, term)
eval (Var var) = Var var

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
  prompt (eval . (\t -> let (term, _) = uniquify t [] 0 in term))  
