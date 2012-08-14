{-# LANGUAGE TemplateHaskell #-}
module Fun.Eval.Rules where

import Lens.Family
import Lens.Family.TH

import Fun.Decl
import Fun.Environment
import Fun.Theory


import Equ.PreExpr
import Equ.Syntax 
import Equ.Matching

import Equ.TypeChecker(getType,unificate)
import Equ.IndType
import Equ.IndTypes
import Equ.Types

import Data.List(find)
import Data.Maybe(fromMaybe)

import Control.Monad((>=>),join)
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Control.Arrow ((&&&),(***),first)
import Control.Applicative((<$>),liftA2)
import Data.Function(on)

data EvOrder = Eager | Normal
             deriving Show

-- | La evaluación de una expresión puede ser correcta o incorrecta.
type EvalM = Either String 

-- | Las reglas que definen el comportamiento de operadores consisten
-- en un mapeo de patrones a expresiones.

data Env = Env { decls :: [FunDecl] }
         deriving Show

data EvalEnv = EvalEnv { _order :: EvOrder
                       , _env   :: Env
                       , _theories :: [Theory]
                       }
$(mkLenses ''EvalEnv)

type EvState a = ReaderT EvalEnv EvalM a

getEnv :: EvState Env
getEnv = asks ((^. env))

getOrder :: EvState EvOrder
getOrder = asks ((^. order))

getTheories :: EvState [Theory]
getTheories = asks ((^. theories))

-- | Una aplicación parcial de una función a varios argumentos.
type PartialApp = (Func,[PreExpr])

-- | Reglas de evaluacion
data Eval = EvConst Constant
          | EvFun Func
          | EvVar Variable
          | EvUnary Operator 
          | EvBinary Operator
          | IfTrue 
          | IfFalse
          | EvParApp PartialApp 
          | EvApp 
          | EvCase

data Evaluation = Evaluation {
      start :: PreExpr
    , result :: Maybe PreExpr
    , evaluation :: Eval
    , premises :: [Evaluation]
    }

fail' :: String -> EvState a
fail' = lift . Left

lookupOp :: Operator -> [OpDecl] -> Maybe ([Variable],PreExpr)
lookupOp op = find eqOp >=> (\(OpDecl _ vs body) -> return (vs,body))
    where eqOp (OpDecl op' _ _) = op == op'

errOpNotInEnv :: Operator -> EvState a
errOpNotInEnv op = fail' $ "Operator not declared: " ++ show op

getResult :: Evaluation -> EvState PreExpr
getResult = maybe (fail' "No result") return . result

parApp :: PreExpr -> EvState Int
parApp (Var f) = arity . varTy . fst' <$> findFun f
    where fst' (x,_,_) = x
parApp (App e _) = flip (-) 1 <$> parApp e
parApp _ = return 0

parApp' :: PreExpr -> EvState (Maybe (Int,(Variable,[Variable],PreExpr)))
parApp' (Var f) = Just . (arity . varTy . fst' &&& id) <$> findFun f
    where fst' (x,_,_) = x
parApp' (App e _) = fmap (first (flip (-) 1)) <$> parApp' e
parApp' _ = return Nothing

getArgs :: PreExpr -> Maybe [PreExpr]
getArgs (Var _) = return []
getArgs (App (Var _) e') = return [e']
getArgs (App e e') = (e':) <$> getArgs e
getArgs _ = Nothing

findFunDecl :: Variable -> FunDecl -> Bool
findFunDecl f (Fun f' _ _ _) = f == f'

findFun :: Variable -> EvState (Variable,[Variable],PreExpr)
findFun f = getEnv >>= \env -> (maybe (fail' $ "Function not declared: " ++ show f ++ show env) getDecl
            . find (findFunDecl f) 
            . decls) env
    where getDecl (Fun f vs e _) = return (f,vs,e)

findOpDecl :: Operator -> EvState ([Variable],PreExpr)
findOpDecl op = getTheories >>= maybe (errOpNotInEnv op) return . lookupOp op . concatMap operators

matching :: PreExpr -> PreExpr -> PreExpr -> Maybe PreExpr
matching e p r = either (const Nothing) (return . applySubst r . fst) $ match p e

matchCouple :: (PreExpr,PreExpr) -> (PreExpr,PreExpr,PreExpr) -> Maybe PreExpr
matchCouple (e,e') (p,p',res) = case subst of 
                                  Left _ -> Nothing
                                  Right s -> return $ applySubst res (fst s)
    where subst = match p e >>= matchWithSubst p' e'                               

firstMatching :: PreExpr -> [(PreExpr,PreExpr)] -> EvState PreExpr
firstMatching e = maybe (fail' "First matching") return . find'' . map (uncurry (matching e))

find'' :: [Maybe a] -> Maybe a
find'' = foldr max' Nothing 
    where max' Nothing (Just x) = Just x
          max' (Just x) Nothing = Just x
          max' _ _ = Nothing

isCan :: PreExpr -> EvState Bool
isCan e = (fromMaybe False . canonical) <$> getTheories
    where canonical ths = getType e >>= getIndType' ths >>= isCanonical e

isCanonical :: PreExpr -> IndType -> Maybe Bool
isCanonical (Var _) _ = return True
isCanonical (Paren e) ty = isCanonical e ty
isCanonical (Con c) ty = return $ c `elem` constants ty
isCanonical (UnOp op e) ty = (isConstructor ty op &&) <$> case opTy op of
                               t1 :-> _ -> getType e >>=
                                          unificate t1 >>=
                                          join . liftToIndType (isCanonical e) 
                               _ -> error "Impossible"
isCanonical (BinOp op e e') ty = (isConstructor ty op &&) <$>
                                 case opTy op of
                                   t1 :-> t2 :-> _ -> getType e >>=
                                                     unificate t1 >>= \t1' ->
                                                     getType e' >>=
                                                     unificate t2 >>= \t2' ->                                                     
                                                     liftToIndType (isCanonical e) t1' `and'`
                                                     liftToIndType (isCanonical e') t2'
                                   _ -> error "Impossible"
isCanonical(App e e') ty = case getType e of
                              Nothing -> error "Impossible"
                              Just (t1 :-> t2) -> getType e' >>=
                                                 unificate t1 >>= \t1' ->
                                                 liftToIndType (isCanonical e') t1' `and'`
                                                 liftToIndType (isNeutral e) (t1 :-> t2)
                              Just t -> return False
isCanonical _ _ = return False


isNeutral :: PreExpr -> IndType -> Maybe Bool
isNeutral (UnOp op _) t = return $ isConstructor t op
isNeutral (BinOp op _ _) t = return $ isConstructor t op
isNeutral (App e e') t = case getType e of
                            Nothing -> error "Impossible"
                            Just (t1 :-> t2) -> getType e' >>= unificate t1 >>= \t1' ->
                                               liftToIndType (isNeutral e) (t1 :-> t2) `and'` 
                                               liftToIndType (isCanonical e') t1'
isNeutral _ _ = return True

          

getIndType' :: [Theory] -> Type -> Maybe IndType
getIndType' ths = join . liftToIndType (indTypeInScope ths) 

liftToIndType :: (IndType -> a) -> Type -> Maybe a
liftToIndType f t = f <$> getIndType t


indTypeInScope :: [Theory] -> IndType -> Maybe IndType
indTypeInScope ths ty = if ty `elem` concatMap indType ths 
                        then Just ty 
                        else Nothing

and' = liftA2 (&&) `on` join