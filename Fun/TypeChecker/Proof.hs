module Fun.TypeChecker.Proof where

import Fun.TypeChecker.Expr
import Equ.Proof.Proof 
import Equ.PreExpr
import Equ.Types
import Equ.IndTypes
import Equ.TypeChecker.Unification

import System.IO.Unsafe

chkBasic :: Type -> Basic -> TIMonad ()
chkBasic t (Ax ax) = return ()
chkBasic t (Theo th) = return ()
chkBasic t (Hyp _) = return ()
chkBasic (TyAtom ATyNat) Evaluate = return ()
chkBasic _ Evaluate = throwError "We cannot type-check this."
chkBasic _ (Evaluation _) = throwError "We cannot type-check this."

chkProof :: Proof -> TIMonad Proof
chkProof Reflex = return Reflex
chkProof p@(Hole _ r e e') = check (toExpr e) >>= \t ->
                             check (toExpr e') >>= \t' ->
                             unifyS t t' >> return p
chkProof p@(Simple _ r e e' prf) = check (toExpr e) >>= \t ->
                                 check (toExpr e') >>= \t' ->
                                 unifyS t t' >> return p
chkProof p@(Trans _ r e e' e'' prf prf') = chkProof prf >>
                                           chkProof prf' >>
                                           return p
chkProof p@(Cases _ r e e' f prfs mprf) = return p
chkProof p@(Ind c r ei ef f prfs) = check (toExpr ei) >>= \t ->
                                    check (toExpr ef) >>= \t' ->
                                    unifyS t t' >>
                                    setTypeS (toExpr ei) >>= \ei' ->
                                    setTypeS (toExpr ef) >>= \ef' ->
                                    setTypeS (toExpr f) >>= \f' ->
                                    return (Ind c r (replace ei ei') (replace ef ef') (replace f f') prfs)
                                 
chkProof p = return p