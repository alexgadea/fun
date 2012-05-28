{-# Language OverloadedStrings #-}
module Fun.FunTheories.FOL(
       folTheory
     , bool
     ) where

import qualified Equ.Theories.FOL as EquFOL
import qualified Equ.Theories as EquTh
import Equ.PreExpr.Symbols(tyListVar)
import Equ.PreExpr
import Equ.Types
import Equ.Syntax

import Fun.IndType
import Fun.Theory

import Data.Maybe(fromJust)
import Data.Text hiding (map)



{- Lógica -}
            
bool :: IndType
bool =  fromJust $ createIndType "Bool" (TyAtom ATyBool) [EquFOL.folTrue, EquFOL.folFalse] []

boolOperators = EquFOL.theoryOperatorsList

boolQuantifiers = EquFOL.theoryQuantifiersList

boolAxioms = EquTh.listAxioms

boolTheorems = []

folTheory = Theory {
            tname = "Lógica"
          , indType = [bool]
          , operators = []
          , quantifiers = boolQuantifiers
          , axioms = boolAxioms
          , theorytheorems = boolTheorems
          }
