
module Fun.Theory where


import Equ.PreExpr
import Equ.Proof
import Equ.Syntax
import Equ.IndType

import Data.Text


{- Una teoria en Fun agrupa todo lo referido a un tipo de dato inductivo, 
   conteniendo los operadores y las funciones definidas para ese tipo, y los
   axiomas y teoremas que permitiran hacer transiciones de programas en los que
   esté involucrado el tipo. -}
data Theory = Theory {
               tname :: Text
             , indType :: [IndType] 
             , operators :: [(Operator,[Variable],PreExpr)] -- En esta lista no se incluye a los constructores.
             , quantifiers :: [Quantifier]
             , axioms :: [Axiom]
             , theorytheorems :: [Theorem]
            }

            
            