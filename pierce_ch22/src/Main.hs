module Main where

import System.IO
import Data.List

type Variable = String

type Context = [(Variable, Type)]
type Constraint = (Type, Type)

data Type = TBool | TNat | TVar Variable | TFun Type Type | TError deriving (Show, Read, Eq)
data Term = Var Variable | Abs Variable Term | App Term Term | Zero | Succ Term | Pred Term | IsZero Term | TrueT | FalseT | If Term Term Term deriving (Show, Read, Eq) 

makeTVar :: Int->Type
makeTVar nextId = TVar ("T" ++ (show nextId))

typeCheckWithConstraints::Term->Context->Int->(Type, [Constraint], Int)
typeCheckWithConstraints t ctx nextId = 
  case t of 
    Var var -> let result = lookup var ctx in case result of Just type1 -> (type1, [], nextId)
                                                             _          -> (TError, [], nextId)
    Abs var t1 -> 
      let nextId2 = nextId + 1 in
        let myTVar = makeTVar nextId2 in
          let (t1_type, t1_constraints, t1_nextId) = typeCheckWithConstraints t1 ((var, myTVar):ctx) nextId2 in
            (TFun myTVar t1_type, t1_constraints, t1_nextId)  
    App t1 t2 ->
      let (t1_type, t1_constraints, t1_nextId) = typeCheckWithConstraints t1 ctx nextId in
        let (t2_type, t2_constraints, t2_nextId) = typeCheckWithConstraints t2 ctx t1_nextId in
          let nextId2 = t2_nextId + 1 in
            let myTVar = makeTVar nextId2 in 
              (myTVar, t1_constraints `union` t2_constraints `union` [(t1_type, TFun t2_type myTVar)], nextId2) 
    Zero -> (TNat, [], nextId)
    Succ t1 ->
      let (t1_type, t1_constraints, t1_nextId) = typeCheckWithConstraints t1 ctx nextId in
        (TNat, [(t1_type, TNat)] `union` t1_constraints, t1_nextId)
    Pred t1 ->
      let (t1_type, t1_constraints, t1_nextId) = typeCheckWithConstraints t1 ctx nextId in
        (TNat, [(t1_type, TNat)] `union` t1_constraints, t1_nextId)
    IsZero t1 ->
      let (t1_type, t1_constraints, t1_nextId) = typeCheckWithConstraints t1 ctx nextId in
        (TBool, [(t1_type, TNat)] `union` t1_constraints, t1_nextId)
    TrueT -> (TBool, [], nextId)
    FalseT -> (TBool, [], nextId)
    If t1 t2 t3 ->
      let (t1_type, t1_constraints, t1_nextId) = typeCheckWithConstraints t1 ctx nextId in
        let (t2_type, t2_constraints, t2_nextId) = typeCheckWithConstraints t2 ctx t1_nextId in
          let (t3_type, t3_constraints, t3_nextId) = typeCheckWithConstraints t3 ctx t2_nextId in
            (t2_type, t1_constraints `union` t2_constraints `union` t3_constraints `union` [(t1_type, TBool), (t2_type, t3_type)], t3_nextId)

substituteType :: Variable->Type->Type->Type
substituteType var1 replaceType targetType =
  case targetType of TFun tfun1 tfun2 -> TFun (substituteType var1 replaceType tfun1) (substituteType var1 replaceType tfun2)
                     TVar tvar -> if tvar == var1 then replaceType else targetType 
                     _ -> targetType

unify :: Type->[Constraint]->Type
unify type1 [] = type1
unify type1 ((lhs, rhs):constraints) =
  if lhs == rhs 
    then unify type1 constraints
    else  
      case (lhs, rhs) of (TVar tvar_lhs, rhs1) -> unify (substituteType tvar_lhs rhs1 type1) (map (\(a,b) -> (substituteType tvar_lhs rhs1 a, substituteType tvar_lhs rhs1 b)) constraints)
                         (lhs1, TVar tvar_rhs) -> unify (substituteType tvar_rhs lhs1 type1) (map (\(a,b) -> (substituteType tvar_rhs lhs1 a, substituteType tvar_rhs lhs1 b)) constraints)
                         (TFun lhs1 lhs2, TFun rhs1 rhs2) -> unify type1 (constraints `union` [(lhs1, rhs1), (lhs2, rhs2)])
                         _ -> TError
                         
typeCheckWithReconstruction :: Term->Type
typeCheckWithReconstruction t = 
  let (type1, constraints, _) = typeCheckWithConstraints t [] 0 in
    unify type1 constraints

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
  prompt (\t -> typeCheckWithReconstruction t)
