
module Fun.Environment where


import Equ.Syntax
import Equ.PreExpr
import Equ.Proof

import Fun.FunTheories.Theories
import Fun.Theory


import qualified Data.Map as M
import Data.Text hiding (map,concatMap)



data Environment = Environment {
                   functions :: M.Map Func PreExpr
                 , specs     :: M.Map Func PreExpr
                 , theorems  :: [Theorem]
                 , props     :: M.Map Text PreExpr
                 , vals      :: M.Map Variable PreExpr
            }
            
            
initTheorems = concatMap theorytheorems [arithTheory,listTheory,folTheory]
            
initEnvironment = Environment {
                    functions = M.empty
                  , specs = M.empty
                  , theorems = initTheorems
                  , props = M.empty
                  , vals = M.empty
                }
                
                
                