
module Fun.Verification (
      Verification (..)
    , module Fun.Verification.Error
    , createVerifications
    , checkVerification
    )
    where

import Fun.Decl
import Fun.Declarations
import Fun.Verification.Verification
import Fun.Verification.Error

import Equ.Expr
import Equ.Proof
import Equ.Rule
import Equ.Theories
import Equ.Theories.FOL 
import qualified Equ.PreExpr as PE

import Data.Text hiding (map,foldl)
import Data.List as L (map, find)
import Data.Either (rights)
import Data.Maybe (fromJust,catMaybes)

createVerifications:: Declarations -> [Verification]
createVerifications decls = do
                let vSpecs = map snd $ specs decls
                let vFuns = map snd $ functions decls
                let vThm = map snd $ theorems decls
                let der = createVer vSpecs vFuns vThm
                catMaybes der
    where
        createVer :: [SpecDecl] -> [FunDecl] -> [ThmDecl] -> [Maybe Verification]
        createVer specs funcs thms = 
            L.map (\s -> L.find (equalFun s) funcs >>= \f ->
                         L.find (equalThm f) thms >>= \(Thm theo) ->
                        Just (Verification s f (thProof theo))) specs
        equalFun :: SpecDecl -> FunDecl -> Bool
        equalFun s f = getFuncDecl s == getFuncDecl f &&
                       getVarsDecl s == getVarsDecl f
        equalThm :: FunDecl -> ThmDecl -> Bool
        equalThm f t = (Just $ getNameDecl t) == getFunDerivingFrom f

-- | Funcion que dada una derivacion dice si es válida o no.
checkVerification :: Verification -> 
                     Either ([VerificationError], Verification) Verification 
checkVerification d = 
            case (checkStartExpr, checkEndExpr, checkHypExpr) of
                ([],[],[]) -> return d
                (sErr,eErr,hypErr) -> Left (sErr ++ eErr ++ hypErr, d)
    where
        prf :: Proof
        prf = proof d
        prg :: PE.PreExpr
        prg = fromJust . getExprDecl $ prog d
        checkStartExpr :: [VerificationError]
        checkStartExpr = do
                let Fun f vs _ _ = prog d
                let fWithArgs = foldl PE.preExprApp (PE.Var f) (map PE.Var vs)
                let Right ei = getStart prf
                if fWithArgs == PE.toExpr ei 
                   then []
                   else [InvalidStartOfProof fWithArgs (PE.toExpr ei)]
        checkEndExpr :: [VerificationError]
        checkEndExpr = do
                let Right ef = getEnd prf
                if prg == PE.toExpr ef
                   then []
                   else [InvalidEndOfProof prg (PE.toExpr ef)]
        checkHypExpr :: [VerificationError]
        checkHypExpr = do
                let Right ctx = getCtx prf
                let Right rel = getRel prf
                let Spec f vs e = spec d
                let fWithArgs = foldl PE.preExprApp (PE.Var f) (map PE.Var vs)
                let hyp = makeHypExpr rel fWithArgs e
                if exprIsHypothesis hyp ctx
                   then []
                   else [MissingSpecHypInProof hyp]
        makeHypExpr :: Relation -> PE.PreExpr -> PE.PreExpr -> Expr
        makeHypExpr r e e' = Expr $ PE.BinOp (relToOp r) e e'
        