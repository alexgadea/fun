{-# Language OverloadedStrings #-}
module Fun.Eval.Sample where


import Equ.Parser
import Equ.PreExpr 
import Equ.Types
import Equ.Proof(printProof)
import Equ.Theories.Arith
import Equ.Theories.List
import Equ.Theories.FOL
import Fun.Eval.Rules
import Fun.Theories(funTheory)
import qualified Fun.Decl as D (FunDecl(..))
import Fun.Eval.Proof

import Control.Monad.Reader
-- import qualified Fun.Eval.Normal as N

suc :: (Operator,[(PreExpr,PreExpr)])
suc = (natSucc, [])

addition :: (Operator,[(PreExpr,PreExpr,PreExpr)])
addition = (natSum, [ (zero,varM,varM)
                    , (suc varN,varM, suc (plus varN varM))
                    ]
            )
    where varM = Var $ var "m" $ TyAtom ATyNat 
          varN = Var $ var "n" $ TyAtom ATyNat 
          zero = Con $ natZero
          suc = UnOp natSucc 
          plus = BinOp natSum


len :: (Operator,[(PreExpr,PreExpr)])
len = (listLength,[ (Con listEmpty,Con natZero)
               , (app varX varXS,suc (UnOp listLength varXS))
               ]
      )
    where varX = Var $ var "x" $ TyVar "A"
          varXS = Var $ var "xs" $ TyList $ TyVar "A"
          suc = UnOp natSucc
          app = BinOp listApp

app = (listApp,[])

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
          zero = Con $ natZero
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
env = initEnv { unary = [suc,len,notOpRules] 
              , binary = [addition,app] 
              , decls = [idFunDecl,fstFunDecl,twiceDecl,isZero]
              }



test = either error (putStrLn . printProof) . flip runReaderT (Eager,env,funTheory) . evalF
