{-# Language OverloadedStrings #-}
module Fun.FunTheories.Arith(
       arithTheory
     , natural
     ) where

import qualified Equ.Theories.Arith as EquArith
import qualified Equ.Theories as EquTh
import Equ.PreExpr.Symbols(tyListVar)
import Equ.PreExpr
import Equ.Types
import Equ.Syntax

import Fun.IndType
import Fun.Theory

import Data.Maybe(fromJust)
import Data.Text hiding (map)



{- ARITMETICA -}

-- Los tipos inductivos los construimos nosotros programadores, pongo fromJust
-- para que si cometemos un error al crear un tipo inductivo, salte a la vista.
natural :: IndType
natural = fromJust $ createIndType "Natural" (TyAtom ATyNat) [EquArith.natZero] [EquArith.natSucc]

varN = var "n" (TyAtom ATyNat)
varM = var "m" (TyAtom ATyNat)
varT = var "t" (TyAtom ATyNat)


{- sum n m = case n of
                0 -> m
                (succ t) -> succ (sum n m)
-}

natSumExpr :: PreExpr
natSumExpr = Case (Var varN) [ (Con EquArith.natZero,
                          Var varM)
                       , (UnOp EquArith.natSucc (Var varT),
                          UnOp EquArith.natSucc (BinOp EquArith.natSum (Var varN) (Var varM)))
                       ]

natSum :: (Operator,[Variable],PreExpr)
natSum = (EquArith.natSum,[varN,varM],natSumExpr)
                           
{- prod n m = case n of
                 0 -> 0
                 1 -> m
                 (succ t) -> sum t (prod t m)
                 -}
natProdExpr :: PreExpr
natProdExpr = Case (Var varN) [ (Con EquArith.natZero,
                           Con EquArith.natZero)
                        , (UnOp EquArith.natSucc (Con EquArith.natZero),
                           Var varM)
                        , (UnOp EquArith.natSucc (Var varT),
                           BinOp EquArith.natSum (Var varT) (BinOp EquArith.natProd (Var varT) (Var varM)))
                       ]

natProd :: (Operator,[Variable],PreExpr)
natProd = (EquArith.natProd,[varN,varM],natProdExpr)


arithOperators = [natSum,natProd]

arithQuantifiers = EquArith.theoryQuantifiersList

arithAxioms = EquTh.arithAxioms

arithTheorems = []

arithTheory :: Theory
arithTheory = Theory {
              tname = "Aritmética"
            , indType = [natural]
            , operators = arithOperators
            , quantifiers = arithQuantifiers
            , axioms = arithAxioms
            , theorytheorems = arithTheorems
            }
            
            
            