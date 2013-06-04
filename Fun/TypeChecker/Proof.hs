module Fun.TypeChecker.Proof where

import Fun.TypeChecker.Expr
import Equ.Proof.Proof 
import Equ.PreExpr
import Equ.Types
import Equ.TypeChecker.Unification

chkBasic :: Type -> Basic -> TIMonad ()
chkBasic t (Ax ax) = return ()
chkBasic t (Theo th) = return ()
chkBasic t (Hyp _) = return ()
chkBasic (TyAtom ATyNat) Evaluate = return ()
chkBasic _ Evaluate = throwError "We cannot type-check this."
chkBasic _ (Evaluation _) = throwError "We cannot type-check this."

chkProof :: Proof -> TIMonad ()
chkProof Reflex = return ()
chkProof (Hole _ r e e') = check (toExpr e) >>= \t ->
                           check (toExpr e') >>= \t' ->
                           unifyS t t' >> return ()
chkProof (Simple _ r e e' prf) = check (toExpr e) >>= \t ->
                                 check (toExpr e') >>= \t' ->
                                 unifyS t t' >> return ()
chkProof (Trans _ r e e' e'' prf prf') = chkProof prf >>
                                         chkProof prf'
chkProof (Cases _ r e e' f prfs mprf) = return ()
chkProof (Ind _ r e e' f prfs) = return ()
chkProof _ = return ()