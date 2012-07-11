
module Fun.Declarations where

import Equ.Syntax
import qualified Equ.PreExpr as PE ( toFocus, PreExpr'(Var,Fun)
                                   , listOfFun, listOfVar, Focus)
import Equ.Proof
import Equ.Types

import Fun.Theories
import Fun.Theory
import Fun.Decl
import Fun.Decl.Error
import Equ.IndType

import qualified Data.Map as M
import Data.Text hiding (map,concatMap)
import qualified Data.List as L (map,elem)
import Data.Either (lefts)
import Data.Maybe (fromJust)

data Declarations = Declarations {
                   specs     :: [SpecDecl]
                 , functions :: [FunDecl]
                 , theorems  :: [ThmDecl]
                 , props     :: [PropDecl]
                 , vals      :: [ValDecl]
                 , indTypes  :: [(Type,IndType)] -- Si luego extendemos para declarar tipos, este campo del environment va agregando cada uno de
                                           -- los nuevos tipos declarados. Por ahora usaremos solo el valor inicial que le pasamos,
                                           -- el cual contiene los tipos basicos de Equ.
            }

instance Show Declarations where
    show decls = "\nSpecs " ++ show (specs decls) ++ "\n" ++
                 "Funs " ++ show (functions decls) ++ "\n" ++
                 "Thms " ++ show (theorems decls) ++ "\n" ++
                 "Props " ++ show (props decls) ++ "\n" ++
                 "Vals " ++ show (vals decls)
            
envAddFun :: Declarations -> FunDecl -> Declarations
envAddFun env f = env {functions = f:(functions env)}

envAddSpec :: Declarations -> SpecDecl -> Declarations
envAddSpec env s = env {specs = s:(specs env)} 

envAddVal :: Declarations -> ValDecl -> Declarations
envAddVal env v = env {vals = v:(vals env)}

envAddTheorem :: Declarations -> ThmDecl -> Declarations
envAddTheorem env p = env {theorems = p:(theorems env)} 

envAddProp :: Declarations -> PropDecl -> Declarations
envAddProp env p = env {props = p:(props env)} 

valsDef :: Declarations -> [Variable]
valsDef = L.map (\(Val v _) -> v) . vals

funcsDef :: Declarations -> [Func]
funcsDef = L.map (\(Fun f _ _ _) -> f) . functions

checkSpecs :: Declarations -> [Either (ErrInDecl SpecDecl) SpecDecl]
checkSpecs ds = L.map (\spec -> 
                case (checkDefVar spec ds, checkDefFunc spec ds) of
                    ([],[]) -> Right spec
                    (vErrs,fErrs) -> Left $ (vErrs ++ fErrs, spec)) $ specs ds
                    
checkFuns :: Declarations -> [Either (ErrInDecl FunDecl) FunDecl]
checkFuns ds = 
    L.map (\fun -> 
    case (checkDefVar fun ds, checkDefFunc fun ds, checkIsPrg  fun) of
        ([],[],True) -> Right fun
        (vErrs,fErrs,_) -> Left $ 
            (vErrs ++ fErrs ++ [InvalidPrgDeclaration], fun)) $ functions ds

checkThm :: Declarations -> [Either (ErrInDecl ThmDecl) ThmDecl]
checkThm = L.map (\thm@(Thm p) -> 
            either (\p -> Left ([InvalidProofForThm p],thm)) (const $ Right thm) 
                (validateProof (thProof p))) . theorems

checkVals :: Declarations -> [Either (ErrInDecl ValDecl) ValDecl]
checkVals ds = L.map (\val -> 
                case (checkDefVar val ds, checkDefFunc val ds) of
                    ([],[]) -> Right val
                    (vErrs,fErrs) -> Left $ (vErrs ++ fErrs, val)) $ vals ds

checkDefVar :: Decl d => d -> Declarations -> [DeclError]
checkDefVar d ds = do
        lefts $ L.map (\(PE.Var v, _) -> 
                    if v `L.elem` valsDef ds
                    then Right ()
                    else Left $ UndeclaredVar v) (PE.listOfVar $ getFocusDecl d)

checkDefFunc :: Decl d => d -> Declarations -> [DeclError]
checkDefFunc d ds = do
        lefts $ L.map (\(PE.Fun f, _) -> 
                    if f `L.elem` funcsDef ds
                    then Right ()
                    else Left $ UndeclaredFunc f) (PE.listOfFun $ getFocusDecl d)

getFocusDecl :: Decl d => d -> PE.Focus
getFocusDecl = PE.toFocus . fromJust . getExprDecl 

checkIsPrg :: Decl d => d -> Bool
checkIsPrg = isPrg . fromJust . getExprDecl

initTheorems :: [Theorem]
initTheorems = concatMap theorytheorems [arithTheory,listTheory,folTheory]
  
mapIndTypes :: [(Type' TyVarName, IndType)]
mapIndTypes = [ (TyAtom ATyNat,natural)
              , (TyAtom ATyBool,bool)
              , (TyList (tyVar "A"), list)
              ]

initDeclarations :: Declarations
initDeclarations = Declarations {
                    functions = []
                  , specs = []
                  , theorems = map Thm initTheorems
                  , props = []
                  , vals = []
                  , indTypes = mapIndTypes
                }
