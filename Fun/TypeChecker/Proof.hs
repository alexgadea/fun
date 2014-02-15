module Fun.TypeChecker.Proof where

import Fun.TypeChecker.Expr
import Equ.Proof.Proof 
import Equ.PreExpr
import Equ.Types

chkBasic :: Type -> Basic -> TIMonad ()
chkBasic _ (Ax _) = return () -- TODO: complete
chkBasic _ (Theo _) = return () -- TODO: complete
chkBasic _ (Hyp _) = return () -- TODO: complete
chkBasic (TyAtom ATyNat) Evaluate = return ()
chkBasic _ Evaluate = throwError "We cannot type-check this."
chkBasic _ (Evaluation _) = throwError "We cannot type-check this."

chkProof :: Proof -> TIMonad Proof
chkProof Reflex = return Reflex
chkProof p@(Hole _ _ e e') = check' e >>= \t ->
                             check' e' >>= \t' ->
                             unifyS t t' >> return p
chkProof p@(Simple _ _ e e' _) = check' e >>= \t ->
                                   check' e' >>= \t' ->
                                   unifyS t t' >> return p
chkProof p@(Trans _ _ _ _ _ prf prf') = chkProof prf >>
                                           chkProof prf' >>
                                           return p
chkProof p@(Cases _ _ _ _ _ _ _) = return p
chkProof (Ind c r ei ef f prfs) = check' ei >>= \t ->
                                  check' ef >>= \t' ->
                                  unifyS t t' >>
                                  setTypeS (toExpr ei) >>= \ei' ->
                                  setTypeS (toExpr ef) >>= \ef' ->
                                  setTypeS (toExpr f) >>= \f' ->
                                  return (Ind c r (replace ei ei') (replace ef ef') (replace f f') prfs)                                 
chkProof p = return p

check' :: Focus -> TIMonad Type
check' f = initCtxE e >> check e
    where e = toExpr f
