-- | Modulo que construye pruebas a partir de una derivación.
module Fun.Eval.Proof(evalToProof,evalF,getEnd'',proofDone) where

import Fun.Eval.Rules
import Fun.Theories(funTheory)
import Fun.Environment
import Equ.Parser


import Equ.Proof hiding (EvalStep(..),Basic(Evaluation))
import qualified Equ.Proof as P (EvalStep(..),Basic(Evaluation)) 
import Equ.Rule (relEval)
import Equ.PreExpr (PreExpr'(..),PreExpr,toFocus)
import qualified Equ.PreExpr as E

import Data.Map (fromList)
import Data.Maybe (isNothing,fromJust)
import Control.Applicative ((<$>))
import Control.Monad ((>=>))
import Control.Monad.Trans.Reader

testEval :: Environment -> String -> String
testEval env = either id printProof . 
               flip runReaderT initEnv .
               evalF . toFocus . parser
    where env' = Env $ getFuncs env
          initEnv = EvalEnv Eager env' funTheory


eval :: PreExpr -> E.Focus -> P.EvalStep -> EvState Proof
{-# INLINE eval #-}
eval e e' = return . Simple beginCtx relEval (toFocus e) e' . P.Evaluation 

evalF :: E.Focus -> EvState Proof
evalF foc = isCan (E.toExpr foc) >>= \canFoc ->
            if canFoc 
            then fail' "Canonical expression"
            else evalToProof (E.toExpr foc) >>= \prf ->
                 getEnd' prf >>= \foc' ->
                 isCan (E.toExpr foc') >>= \canFoc' ->
                 if canFoc' 
                 then return prf
                 else evalF foc' >>= \prf' ->
                      getEnd' prf' >>= \foc'' ->
                      return $ Trans beginCtx relEval foc foc' foc'' prf prf'
             

getEnd' :: Proof -> EvState E.Focus
getEnd' = either (fail' . ("getEnd: "++) . show) return . getEnd 
               
getEnd'' :: Proof -> EvState PreExpr
getEnd'' = either (\_err -> fail' "getEnd") (return . E.toExpr) . getEnd 

proofDone :: Proof -> EvalEnv -> Bool
proofDone prf env = either (const False) id .
                    flip runReaderT env $ 
                    either (const $ return False) (isCan . E.toExpr) $ getEnd prf

evalToProof :: PreExpr -> EvState Proof
evalToProof e@(Var v) = fail' $ "evalVar" ++ show v
evalToProof e@(Con _) = fail' "evalCon"
evalToProof e@(Paren _) = evalSubExpr e E.goDown
evalToProof e@(UnOp op e') =  isCan e' >>= \cane' ->
                              if cane'
                              then findOpDecl op >>= \(vs,body) ->
                                   eval e (applyArgs body  vs [e']) (P.EvUnary op)
                              else evalSubExpr e E.goDown

evalToProof e@(BinOp op e1 e2) = isCan e1 >>= \cane1 ->
                                 isCan e2 >>= \cane2 ->
                                 case (cane1, cane2) of
                                   (True,True) -> findOpDecl op >>= \(vs,body) ->
                                                 eval e (applyArgs body vs [e1,e2]) (P.EvBinary op)
                                   (True,False) -> evalSubExpr e E.goDownR
                                   (False,_) -> evalSubExpr e E.goDown
    where prfe1 = evalToProof e1
          prfe2 = evalToProof e

evalToProof e@(App e1 e2) = parApp' e1 >>= maybe (fail' "parApp'") (\(i,(_,vs,body)) -> 
                            getOrder >>= \ord ->                            
                            case ord of
                              Eager -> fstToReduce e >>= maybe (evalApp i body vs e1 e2) (evalSubExpr e)
                              Normal -> evalApp i body vs e1 e2)

evalToProof e@(If b t f) = case isBoolean b of
                             Nothing -> evalSubExpr e E.goDown 
                             Just b -> eval e (toFocus (bool b t f)) $ bool b P.IfTrue P.IfFalse
evalToProof e@(Case e' cs) = isCan e' >>= \cane' ->
                             if cane'
                             then firstMatching e' cs >>= \exp -> 
                                  eval e (toFocus exp) P.EvCase
                             else evalSubExpr e E.goDown
                  
evalSubExpr :: PreExpr -> (E.Focus -> Maybe E.Focus) -> EvState Proof
evalSubExpr e mv = maybe (fail' "EvalSubExpr") 
                   (\(e',p) -> evalToProof e' >>= \prf' ->
                              return $ Focus beginCtx relEval foc (lastExpr prf',p) prf') $ mv foc
    where foc = toFocus e
          lastExpr = E.toExpr . fromRight . getEnd 

fstToReduce :: PreExpr -> EvState (Maybe (E.Focus -> Maybe E.Focus))
fstToReduce e@(App (Var _) _) = maybe (return Nothing)
                                (\foc ->  isCan (fst foc) >>= \canFoc -> 
                                         if canFoc then return Nothing else return $ Just E.goDownR)
                                $ E.goDownR (toFocus e )
fstToReduce e@(App e' _) = maybe Nothing (Just . (E.goDown >=>)) <$> fstToReduce e'
fstToReduce _ = return Nothing

closure :: [E.Variable] -> PreExpr -> PreExpr -> Maybe E.ExprSubst
closure vs e1 e2 = fromList . zip vs . reverse . (e2:) <$> getArgs e1

evalApp :: Int -> PreExpr -> [E.Variable] -> PreExpr -> PreExpr -> EvState Proof
evalApp i body vs e1 e2 = if i == 1 then evalAppSat body vs e1 e2 else fail' "evalApp"

evalAppSat :: PreExpr -> [E.Variable] -> PreExpr -> PreExpr -> EvState Proof
evalAppSat body vs e1 e2 = maybe (fail' "evalAppSat") 
                           (flip (eval (App e1 e2)) P.EvApp . toFocus . E.applySubst body) 
                           (closure vs e1 e2)

bool :: Bool -> a -> a -> a
{-# INLINE bool #-}
bool b e e' = if b then e else e'

applyArgs :: PreExpr -> [E.Variable] -> [PreExpr] -> E.Focus
applyArgs e vs args = toFocus . E.applySubst e $ fromList $ zip vs args

-- | Unsafe!
fromRight :: Either a b -> b
fromRight = either (const $ error "") id