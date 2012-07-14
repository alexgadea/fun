-- | Modulo que construye pruebas a partir de una derivación.
module Fun.Eval.Proof where

import Fun.Eval.Rules

import Equ.Proof hiding (EvalStep(..),Basic(Evaluation))
import qualified Equ.Proof as P (EvalStep(..),Basic(Evaluation)) 
import Equ.Rule (relEval)
import Equ.PreExpr (PreExpr'(..),PreExpr,toFocus)
import qualified Equ.PreExpr as E

import Data.Map (fromList)
import Data.Maybe (isNothing,fromJust)
import Control.Applicative ((<$>))
import Control.Monad ((>=>))

eval :: PreExpr -> E.Focus -> P.EvalStep -> EvState Proof
{-# INLINE eval #-}
eval e e' = return . Simple beginCtx relEval (toFocus e) e' . P.Evaluation 

evalF :: E.Focus -> EvState Proof
evalF foc = isCan (E.toExpr foc) >>= \canFoc ->
            if canFoc 
            then fail' ""
            else evalToProof (E.toExpr foc) >>= \prf ->
                 getEnd' prf >>= \foc' ->
                 isCan (E.toExpr foc') >>= \canFoc' ->
                 if canFoc' 
                 then return prf
                 else evalF foc' >>= \prf' ->
                      getEnd' prf' >>= \foc'' ->
                      return $ Trans beginCtx relEval foc foc' foc'' prf prf'
             

evaluate = evalF . E.toFocus

getEnd' :: Proof -> EvState E.Focus
getEnd' = either (const $ fail' "") return . getEnd 
               

evalToProof :: PreExpr -> EvState Proof
evalToProof e@(Var _) = fail' "evalVar"
evalToProof e@(Con _) = fail' "evalCon"
evalToProof e@(Fun _) = fail' "evalFun"
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
fstToReduce e@(App (Fun _) _) = maybe (return Nothing)
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