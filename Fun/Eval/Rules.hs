module Fun.Eval.Rules where


import Fun.Decl
import Fun.Environment
import Fun.Theory


import Equ.PreExpr hiding (PreExpr'(Fun))
import qualified Equ.PreExpr as PE (PreExpr'(Fun))
import Equ.Syntax
import Equ.Matching

import Equ.TypeChecker(getType,unificate)
import Equ.IndType
import Equ.IndTypes
import Equ.Types

import Data.List(find)
import Data.Maybe(fromMaybe)

import Control.Monad((>=>))
import Control.Monad.Reader
import Control.Arrow ((&&&),(***),first)
import Control.Applicative((<$>),liftA2)
import Data.Function(on)

data EvOrder = Eager | Normal

type EvState a = ReaderT (EvOrder,Env,[Theory]) EvalM a

getEnv :: EvState Env
getEnv = asks (\(_,env,_) -> env)

getOrder :: EvState EvOrder
getOrder = asks (\(ord,_,_) -> ord)

getTheories :: EvState [Theory]
getTheories = asks (\(_,_,ths) -> ths)

-- | La evaluación de una expresión puede ser correcta o incorrecta.
type EvalM = Either String 

-- | Las reglas que definen el comportamiento de operadores consisten
-- en un mapeo de patrones a expresiones.

data Env = Env { decls :: [FunDecl] }

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
parApp (PE.Fun f) = arity . fst' <$> findFun f
    where fst' (x,_,_) = x
parApp (App e _) = flip (-) 1 <$> parApp e
parApp _ = return 0

parApp' :: PreExpr -> EvState (Maybe (Int,(Func,[Variable],PreExpr)))
parApp' (PE.Fun f) = Just . (arity . fst' &&& id) <$> findFun f
    where fst' (x,_,_) = x
parApp' (App e _) = fmap (first (flip (-) 1)) <$> parApp' e
parApp' _ = return Nothing

getArgs :: PreExpr -> Maybe [PreExpr]
getArgs (PE.Fun _) = return []
getArgs (App (PE.Fun _) e') = return [e']
getArgs (App e e') = (e:) <$> getArgs e
getArgs _ = Nothing

findFunDecl :: Func -> FunDecl -> Bool
findFunDecl f (Fun f' _ _ _) = f == f'

findFun :: Func -> EvState (Func,[Variable],PreExpr)
findFun f = getEnv >>= maybe (fail' $ "Function not declared: " ++ show f) getDecl
            . find (findFunDecl f) 
            . decls
    where getDecl (Fun f vs e _) = return (f,vs,e)

findOpDecl :: Operator -> EvState ([Variable],PreExpr)
findOpDecl op = getTheories >>= maybe (errOpNotInEnv op) return . lookupOp op . concatMap operators

matching :: PreExpr -> PreExpr -> PreExpr -> Maybe PreExpr
matching e p r = either (const Nothing) (return . applySubst r) $ match p e

matchCouple :: (PreExpr,PreExpr) -> (PreExpr,PreExpr,PreExpr) -> Maybe PreExpr
matchCouple (e,e') (p,p',res) = case subst of 
                                  Left _ -> Nothing
                                  Right s -> return $ applySubst res s
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
isCanonical(PE.Fun _) _ = return True
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
isCanonical _ _ = return False


isNeutral :: PreExpr -> IndType -> Maybe Bool
isNeutral (PE.Fun _) _ = return False
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