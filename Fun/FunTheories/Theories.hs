{-# Language OverloadedStrings #-}
module Fun.FunTypes.Nat(
       arithTheory
     , listTheory
     , folTheory
     ) where

import qualified Equ.Theories.Arith as EquArith
import qualified Equ.Theories.List as EquList
import qualified Equ.Theories.FOL as EquFOL
import qualified Equ.Theories as EquTh
import Equ.PreExpr.Symbols(tyListVar)
import Equ.Types

import Fun.IndType
import Fun.Theory

import Data.Maybe(fromJust)
import Data.Text hiding (map)



{- ARITMETICA -}

-- Los tipos inductivos los construimos nosotros programadores, pongo fromJust
-- para que si cometemos un error al crear un tipo inductivo, salte a la vista.
natural :: IndType
natural = fromJust $ createIndType "Natural" (TyAtom ATyNat) [EquArith.natZero] [EquArith.natSucc]

arithOperators = [EquArith.natSum,EquArith.natProd]

arithFunctions = []

arithQuantifiers = EquArith.theoryQuantifiersList

arithAxioms = EquTh.arithAxioms

arithTheorems = []

arithTheory :: Theory
arithTheory = Theory {
              tname = "Aritmética"
            , indType = natural
            , operators = arithOperators
            , functions = arithFunctions
            , quantifiers = arithQuantifiers
            , axioms = arithAxioms
            , theorems = arithTheorems
            }
            
            
{- LISTAS -}
            
            
list :: IndType
list = fromJust $ createIndType "Lista" (tyListVar "A") [EquList.listEmpty] [EquList.listApp]

listOperators = [ EquList.listIndex, EquList.listConcat, EquList.listLength
                , EquList.listTake, EquList.listDrop]
                
listFunctions = []
            
listQuantifiers = EquList.theoryQuantifiersList

listAxioms = EquTh.listAxioms

listTheorems = []

listTheory = Theory {
             tname = "Listas"
           , indType = list
           , operators = listOperators
           , functions = listFunctions
           , quantifiers = listQuantifiers
           , axioms = listAxioms
           , theorems = listTheorems
           }
           
           
{- Lógica -}
            
bool :: IndType
bool =  fromJust $ createIndType "Bool" (TyAtom ATyBool) [EquFOL.folTrue, EquFOL.folFalse] []

boolOperators = EquFOL.theoryOperatorsList

boolFunctions = []

boolQuantifiers = EquFOL.theoryQuantifiersList

boolAxioms = EquTh.listAxioms

boolTheorems = []

folTheory = Theory {
            tname = "Lógica"
          , indType = bool
          , operators = boolOperators
          , functions = boolFunctions
          , quantifiers = boolQuantifiers
          , axioms = boolAxioms
          , theorems = boolTheorems
          }
