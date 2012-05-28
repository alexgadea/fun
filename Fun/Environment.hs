
module Fun.Environment where


import Equ.Syntax
import Equ.PreExpr
import Equ.Proof
import Equ.Types

import Fun.Theories
import Fun.Theory
import Fun.IndType


import qualified Data.Map as M
import Data.Text hiding (map,concatMap)



data Environment = Environment {
                   functions :: M.Map Func PreExpr
                 , specs     :: M.Map Func PreExpr
                 , theorems  :: [Theorem]
                 , props     :: M.Map Text PreExpr
                 , vals      :: M.Map Variable PreExpr
                 , indTypes  :: [(Type,IndType)]  -- Map entre cada tipo de Equ y un IndType. No puedo usar Map porque Type no es instance of Ord.
                                                  -- Si luego extendemos para declarar tipos, este campo del environment va agregando cada uno de
                                                  -- los nuevos tipos declarados. Por ahora usaremos solo el valor inicial que le pasamos,
                                                  -- el cual contiene los tipos basicos de Equ.
            }
            
            
initTheorems = concatMap theorytheorems [arithTheory,listTheory,folTheory]
  

mapIndTypes = [ (TyAtom ATyNat,natural)
              , (TyAtom ATyBool,bool)
              , (TyList (tyVar "A"), list)
              ]
initEnvironment = Environment {
                    functions = M.empty
                  , specs = M.empty
                  , theorems = initTheorems
                  , props = M.empty
                  , vals = M.empty
                  , indTypes = mapIndTypes
                }
                
                
                