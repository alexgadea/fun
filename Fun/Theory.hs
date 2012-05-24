
module Fun.Theory where

import Equ.Proof
import Equ.Syntax
import Fun.IndType

import Data.Text


{- Una teoria en Fun agrupa todo lo referido a un tipo de dato inductivo, 
   conteniendo los operadores y las funciones definidas para ese tipo, y los
   axiomas y teoremas que permitiran hacer transiciones de programas en los que
   esté involucrado el tipo. -}
data Theory = Theory {
               tname :: Text
             , indType :: IndType
             , operators :: [Operator] -- En esta lista no se incluye a los constructores.
             , quantifiers :: [Quantifier]
             , axioms :: [Axiom]
             , theorytheorems :: [Theorem]
            }
            
            
            