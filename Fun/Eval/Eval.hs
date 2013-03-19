{-# LANGUAGE OverloadedStrings #-}
module Fun.Eval.Eval where

import Equ.PreExpr
import Equ.PreExpr.Symbols(natZero)
import Equ.Expr
import Equ.IndTypes(getIndType)
import Equ.IndType
import Equ.TypeChecker(getType)
import Equ.Types
import Equ.Theories.Arith
import Equ.Matching(match)
import Equ.Parser

import Prelude hiding(sum)

import Control.Monad.Trans.Reader
import Control.Monad.Trans.Class(lift)
import Control.Monad.Trans.State
import System.IO.Unsafe(unsafePerformIO)

import qualified Data.Map as M
import qualified Data.Set as S

import Fun.Decl
import Fun.Eval.Rules

-- | El environment tendrá las variables que son simbolo de función
--   con sus definiciones.
type EvalEnv = M.Map Variable ([Variable],PreExpr)

type EvalMonad a = StateT EvalEnv Maybe a


-- | Esta sería la función principal de evaluación
--   Toma una expresión cualquiera y devuelve una expresión canónica.
--   Se asume que las expresiones ESTAN BIEN TIPADAS
eval :: EvalEnv -> PreExpr -> PreExpr
eval env e = 
    maybe e
          (\(e',env') -> eval env' e')
          (runStateT (evalStep e) env)
                

isCanonical :: PreExpr -> EvalMonad Bool
isCanonical e@(Con c) = 
    lift (getType e >>= getIndType) >>=
    \it -> if c `elem` (constants it)
              then return True
              else return False
isCanonical e@(UnOp op e') =
    -- chequeamos que el operador sea un constructor del tipo
    lift (getType e >>= getIndType) >>=
     \it -> if isConstructor it op
               then isCanonical e'
               else return False
isCanonical e@(BinOp op e' e'') =
     lift (getType e >>= getIndType) >>=
     \it -> if isConstructor it op
               then isCanonical e' >>= \isce' ->
                    isCanonical e'' >>= return . ((&&) isce')
               else return False
-- Una variable es canónica si es un símbolo de función
-- (es una expresión lambda)
isCanonical e@(Var x) =
    get >>=
    return . (M.member x)
    
isCanonical _ = return False


-- | Un paso de evaluación.
--   Si la expresión que se quiere evaluar no tiene las subexpresiones
--   canónicas, entonces el paso se aplicará a la subexpresión (en el marco de la teoria
--   presentada en la tesis, corresponde a aplicar el paso de evaluacion "E-CONTEXT"
evalStep :: PreExpr -> EvalMonad PreExpr
evalStep e@(UnOp op e') = 
    isCanonical e' >>= \iscan ->
    if iscan
       then lift (matchRules e unOpRules)    
       else evalStep e' >>= return . (UnOp op)
evalStep e@(BinOp op e1 e2) =
    isCanonical e1 >>= \iscane1 ->
    if iscane1
       then isCanonical e2 >>= \iscane2 ->
            if iscane2
               then lift (matchRules e binOpRules)
               else evalStep e2 >>=
                    return . (BinOp op e1)
       else evalStep e1 >>=
            return . (flip (BinOp op) e2)
evalStep e@(If b e1 e2) =
    isCanonical b >>= \iscanb ->
    if iscanb
       then isCanonical e1 >>= \iscane1 ->
            if iscane1
               then isCanonical e2 >>= \iscane2 ->
                    if iscane2
                       then lift (matchRules e ifRules)
                       else evalStep e2 >>=
                            return . (If b e1)
            else evalStep e1 >>=
                 return . (flip (If b) e2)
       else evalStep b >>= \bcan ->
            return (If bcan e1 e2)
            
{- | En la tesis, tenemos expresiones lambda para expresar la evaluación de funciones.
     Aqui una variable puede ser aplicada si está en el environment de declaraciones de funciones.
     Si la función es de un solo argumento, la aplicación es directa (se reemplaza la variable por el valor
     en la expresión que define a la función).
     Si la función es de más de un argumento, se crea una nueva función, con un nombre fresco, que toma un argumento
     menos. Por ejemplo:
       g x y = x + y
       
     Queremos evaluar g@0@0. (esto se parsea: (g@0)@0 )
     
     Lo que hacemos entonces es crear una nueva función:
       g' y = 0 + y
       
     y la expresión que queríamos evaluar, se evalúa a:
       g'@0
       
     que al tener ya un solo parámetro, se evalúa trivialmente.
-}
evalStep e@(App v@(Var x) e2) =
    isCanonical v >>= \iscanv ->
    if iscanv
       then isCanonical e2 >>= \iscane2 ->
            if iscane2
               -- Podemos aplicar la función
               then applyFun x e2
               else evalStep e2 >>=
                    return . (App v)
       -- Si (Var x) no es una expresion canonica, significa que la variable
       -- no esta declarada como funcion, por lo tanto no se podrá evaluar.
       -- evalStep v dará Nothing
       else evalStep v
evalStep e@(App e1 e2) =
    isCanonical e1 >>= \iscane1 ->
    if iscane1
       -- Si e1 es canónica pero no es una variable, no se puede aplicar.
       then lift Nothing
       else evalStep e1 >>= return . (flip App e2)
evalStep e@(Case e' ps) =
    matchPatterns e' ps >>= \(ei,subst) ->
    return (applySubst ei subst)
    
    -- matchPatterns busca por un patron en la lista que matchee con la expresión e.
    -- Si lo encuentra retorna la expresión correspondiente al patrón y la substitución del matching.
    -- Si no lo encuentra Nothing
    where matchPatterns :: PreExpr -> [(PreExpr,PreExpr)] -> EvalMonad (PreExpr,ExprSubst)
          matchPatterns e [] = lift Nothing
          matchPatterns e ((p1,e1):ps) =
              either (const $ matchPatterns e ps)
                     (\(subst,_) -> return (e1,subst))
                     (match p1 e)
evalStep (Paren e) = evalStep e
evalStep _ = lift Nothing
                      


applyFun :: Variable -> PreExpr -> EvalMonad PreExpr
applyFun v e =
    get >>= \env ->
    lift (M.lookup v env) >>= \(vars,edef) ->
    case vars of
         [] -> return edef
         [x] -> return (applySubst edef (subst x))
         (y:vs) -> return (freshVar $ S.fromList $ M.keys env) >>= \vnew ->
                   -- creamos la nueva funcion, la cual tiene un parámetro menos
                   -- y su expresión de definición es la misma que v, pero reemplazando
                   -- la variable 'y' por la expresión e
                   modify (M.insert vnew (vs,(applySubst edef $ subst y))) >>
                   return (Var vnew)
         
    where subst x = M.fromList [(x,e)]


-- | Crea un EvalEnv a partir de una lista de declaraciones de funciones
createEvalEnv :: [FunDecl] -> EvalEnv
createEvalEnv [] = M.empty
createEvalEnv ((Fun v vs e _):fs) = M.insert v (vs,e) (createEvalEnv fs)

    
testEvalStep expr = evalStateT (evalStep expr) M.empty
                    
testEval = eval M.empty

test1 e = evalStateT (evalStep e) (M.fromList [(varF,([varX,varY],expr))])
    where varF = var "f" $ (TyAtom ATyNat) :-> (TyAtom ATyNat)
          varX = var "x" $ TyAtom ATyNat
          varY = var "y" $ TyAtom ATyNat
          Expr expr = successor (sum (Expr $ Var varX) (Expr $ Var varY))

