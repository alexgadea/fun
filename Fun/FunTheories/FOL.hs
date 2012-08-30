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

import Equ.IndType
import Equ.IndTypes(bool)
import Fun.Theory
import Fun.Decl

import Data.Maybe(fromJust)
import Data.Text hiding (map)



{- Lógica -}


varP = var "p" (TyAtom ATyBool)
varQ = var "q" (TyAtom ATyBool)


{- or p q = case p of
              False -> q
              True  -> True
-}

folOrExpr :: PreExpr
folOrExpr = Case (Var varP)
             [ (Con EquFOL.folFalse, Var varQ)
             , (Con EquFOL.folTrue,Con EquFOL.folTrue)
             ]

folOr :: OpDecl 
folOr = OpDecl EquFOL.folOr [varP,varQ] folOrExpr
                           
{- and p q = case n of
                 False -> Flase
                 True -> q
                 -}
folAndExpr :: PreExpr
folAndExpr = Case (Var varP) [ (Con EquFOL.folFalse, Con EquFOL.folFalse)
                             , (Con EquFOL.folTrue,Con EquFOL.folTrue)
                              ]

folAnd :: OpDecl
folAnd = OpDecl EquFOL.folAnd [varP,varQ] folAndExpr


boolOperators = EquFOL.theoryOperatorsList

boolQuantifiers = EquFOL.theoryQuantifiersList

boolAxioms = EquTh.listAxioms

boolTheorems = []

folTheory = Theory {
            tname = "Lógica"
          , indType = [bool]
          , operators = [folOr, folAnd]
          , quantifiers = boolQuantifiers
          , axioms = boolAxioms
          , theorytheorems = boolTheorems
          }
