
module Fun.Derivation (
      Derivation(..)
    , module Fun.Derivation.Monad
    , module Fun.Derivation.Error
    , createDerivations
    , checkDerivation
    )
    where

import Fun.Decl
import Fun.Declarations
import Fun.Derivation.Derivation
import Fun.Derivation.Monad
import Fun.Derivation.Error

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

createDerivations :: Declarations -> [Derivation]
createDerivations decls = do
                let vSpecs = rights $ checkSpecs decls
                let vFuns = rights $ checkFuns decls
                let vThm = rights $ checkThm decls
                let der = createDer vSpecs vFuns vThm
                catMaybes der
    where
        createDer :: [SpecDecl] -> [FunDecl] -> [ThmDecl] -> [Maybe Derivation]
        createDer specs funcs thms = 
            L.map (\s -> L.find (equalFun s) funcs >>= \f ->
                         L.find (equalThm f) thms >>= \(Thm theo) ->
                        Just (Derivation s f (thProof theo))) specs
        equalFun :: SpecDecl -> FunDecl -> Bool
        equalFun s f = getFuncDecl s == getFuncDecl f &&
                       getVarsDecl s == getVarsDecl f
        equalThm :: FunDecl -> ThmDecl -> Bool
        equalThm f t = (Just $ getNameDecl t) == getFunDerivingFrom f

-- | Funcion que dada una derivacion dice si es válida o no.
checkDerivation :: Derivation -> Either ([DerivationError], Derivation) Derivation
checkDerivation d = 
            case (checkStartExpr, checkEndExpr, checkHypExpr) of
                ([],[],[]) -> return d
                (sErr,eErr,hypErr) -> Left (sErr ++ eErr ++ hypErr, d)
    where
        prf :: Proof
        prf = proof d
        prg :: PE.PreExpr
        prg = fromJust . getExprDecl $ prog d
        checkStartExpr :: [DerivationError]
        checkStartExpr = do
                let Fun f vs _ _ = prog d
                let fWithArgs = foldl PE.preExprApp (PE.Var f) (map PE.Var vs)
                let Right ei = getStart prf
                if fWithArgs == PE.toExpr ei 
                   then []
                   else [InvalidStartOfProof fWithArgs (PE.toExpr ei)]
        checkEndExpr :: [DerivationError]
        checkEndExpr = do
                let Right ef = getEnd prf
                if prg == PE.toExpr ef
                   then []
                   else [InvalidEndOfProof prg (PE.toExpr ef)]
        checkHypExpr :: [DerivationError]
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
        