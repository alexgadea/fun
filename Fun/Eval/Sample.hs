{-# Language OverloadedStrings #-}
module Fun.Eval.Sample where


import Equ.Parser
import Equ.PreExpr 
import Equ.Types
import Equ.Proof(printProof)
import Equ.Theories.Arith
import Equ.Theories.List
import Equ.Theories.FOL
import Equ.IndType
import Fun.Eval.Rules
import Fun.Theories(funTheory)
import qualified Fun.Decl as D (FunDecl(..))
import Fun.Eval.Proof

import Control.Monad.Reader

idFunDecl = D.Fun idFun [varX] (Var varX) Nothing
    where idFun = Func "ID" (TyVar "A" :-> TyVar "A")
          varX = var "x" $ TyVar "A"


fstFunDecl = D.Fun fstFun [varX,varY] (Var varX) Nothing
    where fstFun = Func "FST" (TyVar "A" :-> TyVar "B" :-> TyVar "A")
          varX = var "x" $ TyVar "A"
          varY = var "y" $ TyVar "B"

twiceDecl = D.Fun twice [varX] (BinOp natSum (Var varX) (Var varX)) Nothing
    where varX = var "x" $ TyAtom ATyNat

twice = Func "DUPLICATE" (TyAtom ATyNat :-> TyAtom ATyNat)


isZeroF = Func "IsZero" (TyAtom ATyNat :-> TyAtom ATyBool)
isZero = D.Fun isZeroF [varX] (Case (Var varX) [ (zero,true)
                                               , (sucY,false)
                                               ]) Nothing
    where
          zero = Con natZero
          varX = var "x" $ TyAtom ATyNat
          varY = Var $ var "y" $ TyAtom ATyNat
          sucY = UnOp natSucc varY
          true = Con folTrue
          false = Con folFalse  

notOp = UnOp folNeg
notOpRules :: (Operator,[(PreExpr,PreExpr)])
notOpRules = (folNeg, [(true,false),(false,true)])
    where true = Con folTrue
          false = Con folFalse


env :: Env
env = initEnv { decls = [idFunDecl,fstFunDecl,twiceDecl,isZero]
              }



test f p = either error (putStrLn . p) . flip runReaderT (Eager,env,funTheory) . f
