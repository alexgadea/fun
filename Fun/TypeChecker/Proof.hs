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

chkProof :: Env -> Proof -> TIMonad Proof
chkProof _ Reflex = return Reflex
chkProof env p@(Hole _ _ e e') = checkWithEnv' env e >>= \t ->
                                 checkWithEnv' env e' >>= \t' ->
                                 unifyS t t' >> return p
chkProof env (Simple c r e e' b) = checkWithEnv' env e >>= \t ->
                                   checkWithEnv' env e' >>= \t' ->
                                   unifyS t t' >>
                                   setTypeS (toExpr e) >>= \e1 ->
                                   setTypeS (toExpr e') >>= \e2 ->
                                   return (Simple c r (replace e e1)
                                                      (replace e' e2)
                                                      b)
chkProof env (Trans c r e1 e2 e3 prf prf') = checkWithEnv' env e1 >>= \t1 ->
                                             checkWithEnv' env e2 >>= \t2 ->
                                             checkWithEnv' env e3 >>= \t3 ->
                                             unifyListS [t1,t2,t3] >>
                                             setTypeS (toExpr e1) >>= \e1' ->
                                             setTypeS (toExpr e2) >>= \e2' ->
                                             setTypeS (toExpr e3) >>= \e3' ->
                                             chkProof env prf >>= \prf1 ->
                                             chkProof env prf' >>= \prf2 ->
                                             return (Trans c r (replace e1 e1')
                                                               (replace e2 e2')
                                                               (replace e3 e3')
                                                               prf1 
                                                               prf2)
chkProof _ p@(Cases _ _ _ _ _ _ _) = return p
chkProof env (Ind c r ei ef f prfs) = checkWithEnv' env ei >>= \t ->
                                      checkWithEnv' env ef >>= \t' ->
                                      unifyS t t' >>
                                      setTypeS (toExpr ei) >>= \ei' ->                                      
                                      setTypeS (toExpr ef) >>= \ef' ->                                      
                                      setTypeS (toExpr f) >>= \f' ->
                                      return (Ind c r (replace ei ei') (replace ef ef') (replace f f') prfs)                                 
chkProof _ p = return p

checkWithEnv' :: Env -> Focus -> TIMonad Type
checkWithEnv' env f = checkWithEnv env (toExpr f)
