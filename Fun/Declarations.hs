
module Fun.Declarations where

import Equ.Syntax
import Equ.PreExpr
import Equ.Proof
import Equ.Types

import Fun.Theories
import Fun.Theory
import Fun.Decl
import Equ.IndType

import qualified Data.Map as M
import Data.Text hiding (map,concatMap)

data Declarations = Declarations {
                   functions :: [FunDecl]
                 , specs     :: [SpecDecl]
                 , theorems  :: [ThmDecl]
                 , props     :: [PropDecl]
                 , vals      :: [ValDecl]
                 , indTypes  :: [(Type,IndType)] -- Si luego extendemos para declarar tipos, este campo del environment va agregando cada uno de
                                           -- los nuevos tipos declarados. Por ahora usaremos solo el valor inicial que le pasamos,
                                           -- el cual contiene los tipos basicos de Equ.
            }

            
envAddFun :: Declarations -> FunDecl -> Declarations
envAddFun env f = env {functions = f:(functions env)}

envAddSpec :: Declarations -> SpecDecl -> Declarations
envAddSpec env s = env {specs = s:(specs env)} 

envAddVal :: Declarations -> ValDecl -> Declarations
envAddVal env v = env {vals = v:(vals env)}

envAddProp :: Declarations -> PropDecl -> Declarations
envAddProp env p = env {props = p:(props env)} 

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
