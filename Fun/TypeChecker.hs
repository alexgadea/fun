{-# Language TemplateHaskell,DoAndIfThenElse #-}
-- | Chequeo de tipos para un módulo. Inspirado en ``Typing Haskell in Haskell''.
module Fun.TypeChecker where

import Fun.TypeChecker.CallGraph
import Fun.TypeChecker.Expr
import Fun.Decl
-- import Fun.Environment

import Equ.PreExpr
import Equ.Syntax(VarName)
import Equ.Types
import Equ.Proof(Basic(..))

import Data.Map (Map,fromList,delete,empty,lookup)
import qualified Data.Map as M
import Control.Monad.Trans.State
import Control.Monad.Trans.Class
import Data.Function

import Lens.Family
import Lens.Family.TH

import System.IO.Unsafe

type Ass = Map VarName [Type]
checkDecl :: Ass -> Variable -> [Variable] -> PreExpr -> TIMonad Ass
checkDecl ass fun args body = case varTy fun of 
                                TyUnknown -> checkUntypedDecl ass fun args body
                                t -> checkTypedDecl ass fun t args body

checkSpecDecl :: Ass -> SpecDecl -> TIMonad Ass
checkSpecDecl ass (Spec fun args body) = checkDecl ass fun args body

checkFunDecl :: Ass -> FunDecl -> TIMonad Ass
checkFunDecl ass (Fun fun args body _) = checkDecl ass fun args body

checkTypedDecl :: Ass -> Variable -> Type -> [Variable] -> PreExpr -> TIMonad Ass
checkTypedDecl ass fun ty args body = if arity ty /= length args
                                     then throwError "Unexpected number of arguments"
                                     else do 
                                       let argsTy = argsTypes ty
                                       let varTy = fromList $ (varName fun,ty): zipWith (\v t -> ((varName v),t)) args argsTy 
                                       ty' <- checkWithEnv varTy body
                                       if exponential ty' argsTy == ty
                                       then do localState args
                                               ass' <- gets (vars . ctx)
                                               s <- gets subst
                                               return (updateAss (M.union ass ass') s)
                                       else throwError $ "Different resulting types: " ++ show ty ++ " vs. " ++ show ty'

checkUntypedDecl :: Ass -> Variable -> [Variable] -> PreExpr -> TIMonad Ass
checkUntypedDecl ass fun args body = do ty <- checkWithFreshEnv ass fun args body
                                        s <- gets subst
                                        localState args
                                        ass' <- gets (vars . ctx)
                                        return (updateAss (M.union ass ass') s)


checkMutual :: Ass -> [FunDecl] -> TIMonad Ass
checkMutual ass [] = return ass
checkMutual ass (f:fs) = checkFunDecl ass f >>= \ass' ->
                         checkMutual ass' fs

checkMutuals ass [] = return ass
checkMutuals ass (fs:fss) = checkMutual ass fs >>= \ass' -> 
                            checkMutuals ass' fss

tcheckModule :: [FunDecl] -> TIMonad Ass
tcheckModule = checkMutuals empty . reverse . mutualBlocks 

updateTypes :: [FunDecl] -> Ass -> [FunDecl]
updateTypes fs ass = map updDecl fs
    where updDecl f = maybe f (changeTypeDecl f . head) $ M.lookup (getFunName f) ass
          getFunName (Fun f _ _ _) = varName f
                                                                    

changeTypeDecl :: FunDecl -> Type -> FunDecl
changeTypeDecl (Fun f args b i) ty = Fun (setVarType f ty) (zipWith setVarType args (argsTypes ty)) b i
    where setVarType v t = v { varTy = t}

argsTypes :: Type -> [Type]
argsTypes = reverse . go []
    where go :: [Type] -> Type -> [Type]
          go ts (t :-> t') = go (t:ts) t'
          go ts _ = ts

resType :: Type -> Maybe Type
resType (_ :-> t') = Just t'
resType _ = Nothing

exponential :: Type -> [Type] -> Type
exponential = foldl (:->) 

withoutLocal :: Ass -> [Variable] -> Ass
withoutLocal = foldr (delete . varName)

localState :: [Variable] -> TIMonad ()
localState args = modify (\st -> st { ctx = (ctx st) {vars = withoutLocal (vars (ctx st)) args} })

typeCheckDeclarations :: [FunDecl] -> Either [TCError] [FunDecl]
typeCheckDeclarations env = case runStateT (tcheckModule (reverse env)) (TCState empty initCtx 0) of
                              Left err -> Left [err]
                              Right (a,s) -> Right $ updateTypes env a
-- Right $ (unsafePerformIO ((putStrLn $ show a) >> return []))++env

-- | Actualiza los tipos en el contexto.
updateCtx :: TCCtx -> TySubst -> TCCtx
updateCtx ctx subst = ctx { vars = M.map (map (rewrite subst)) (vars ctx) }

updateAss :: Ass -> TySubst -> Ass
updateAss vs s = M.map (map (rewrite s)) vs


