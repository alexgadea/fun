{-# Language OverloadedStrings #-}
module Fun.FunTheories.List(
       listTheory
     , list
     ) where

import qualified Equ.Theories.Arith as EquArith
import qualified Equ.Theories.List as EquList
import qualified Equ.Theories as EquTh
import Equ.PreExpr.Symbols(tyListVar)
import Equ.PreExpr
import Equ.Types
import Equ.Syntax

import Equ.IndType
import Equ.IndTypes(list)
import Fun.Theory
import Fun.FunTheories.Arith

import Data.Maybe(fromJust)
import Data.Text hiding (map)



varN = var "n" (TyAtom ATyNat)
varT = var "t" (TyAtom ATyNat)
varX = var "x" (tyVar "A")
varXS = var "xs" (tyListVar "A")
varYS = var "ys" (tyListVar "A")
              
              
              
{- index n ys = case xs of
                    (x:xs) -> case n of
                                0 -> x
                                (succ t) -> index t xs
                        -}
listIndex :: (Operator,[Variable],PreExpr)
listIndex = (EquList.listIndex,[varN,varYS],exprListIndex)
    where 
        exprListIndex :: PreExpr
        exprListIndex = Case (Var varYS) 
                                [ (BinOp EquList.listApp (Var varX) (Var varXS)
                                , exprListIndex')]
                    
        exprListIndex' :: PreExpr
        exprListIndex' = Case (Var varN) 
                                [(Con EquArith.natZero, Var varX)
                            , (UnOp EquArith.natSucc (Var varT),
                                BinOp EquList.listIndex (Var varT) (Var varXS))
                            ]

{- concat xs ys = case xs of
                      [] -> ys
                      (x:xs) -> x:(concat xs ys)
                      -}
                            
-- listConcat :: (Operator,[Variable],PreExpr)
-- listConcat = (EquList.listConcat,

-- FALTA DEFINIR EL RESTO DE LOS OPERADORES.
                            

listOperators = [ EquList.listIndex, EquList.listConcat, EquList.listLength
                , EquList.listTake, EquList.listDrop]
                
listQuantifiers = EquList.theoryQuantifiersList

listAxioms = EquTh.listAxioms

listTheorems = []

listTheory = Theory {
             tname = "Listas"
           , indType = [list,natural]
           , operators = []
           , quantifiers = listQuantifiers
           , axioms = listAxioms
           , theorytheorems = listTheorems
           }
           