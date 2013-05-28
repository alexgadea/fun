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

import Data.Map (Map,fromList,delete,empty)
import qualified Data.Map as M
import Control.Monad.Trans.State
import Control.Monad(replicateM)
import Data.Foldable (foldrM)

import Control.Lens hiding (rewrite)

type Ass = Map VarName [Type]

checkDecl :: Variable -> [Variable] -> PreExpr -> TIMonad ()
checkDecl fun args body = gets funcs >>= \ass -> 
                          case M.lookup (varName fun) ass of
                                Just (t:_) -> checkTypedDecl ass fun t args body
                                _ -> throwError $ "Función que no está en la lista de suposiciones" 


checkSpecDecl :: SpecDecl -> TIMonad ()
checkSpecDecl (Spec fun args body) = checkDecl fun args body

checkFunDecl :: FunDecl -> TIMonad ()
checkFunDecl (Fun fun args body _) = checkDecl fun args body

checkTypedDecl :: Ass -> Variable -> Type -> [Variable] -> PreExpr -> TIMonad ()
checkTypedDecl ass fun ty args body = if arity ty /= length args
                                      then throwError $ "Unexpected number of arguments: " ++ show ty ++ " <> " ++ show args
                                      else do 
                                       let argsTy = argsTypes ty
                                       let varsTy = fromList $ (varName fun,ty): zipWith (\v t -> (varName v,t)) args argsTy 
                                       ty' <- checkWithEnv varsTy body
                                       s' <- unifyS ty (exponential ty' argsTy)
                                       localState args
                                       ass' <- gets (vars . ctx)
                                       updAss $ updateAss s' (M.union ass ass')

checkBlock ::  [FunDecl] -> TIMonad ()
checkBlock fs = gets funcs >>= \ass -> 
                foldrM addAssumption ass fs >>= \ass' ->
                updAss ass' >>
                mapM_ checkFunDecl fs

    where addAssumption :: FunDecl -> Ass -> TIMonad Ass
          addAssumption f ass = let fname = f ^. funDeclName
                                in if varTy fname /= TyUnknown
                                   then return $ M.insert (varName fname) [varTy fname] ass
                                   else let args = f ^. funDeclArgs
                                        in replicateM (length args) getFreshTyVar >>= \ts ->
                                           getFreshTyVar >>= \tr ->
                                           return $ M.insert (varName fname) [exponential tr ts] ass

tcheckModule :: [FunDecl] -> TIMonad ()
tcheckModule env = mapM_ checkBlock . reverse . mutualBlocks $ env


updateTypes :: [FunDecl] -> Ass -> [FunDecl]
updateTypes fs ass = map updDecl fs
    where updDecl f = maybe f (flip changeTypeDecl f . head) $ M.lookup (f ^. funDeclName ^. to varName) ass
                                                                    

changeTypeDecl :: Type -> FunDecl -> FunDecl
changeTypeDecl ty = (funDeclName %~ setVarType ty) . (funDeclArgs %~ (zipWith setVarType (argsTypes ty)))
    where setVarType t v = v { varTy = t}

withoutLocal :: Ass -> [Variable] -> Ass
withoutLocal = foldr (delete . varName)

localState :: [Variable] -> TIMonad ()
localState args = modify (\st -> st { ctx = (ctx st) {vars = withoutLocal (vars (ctx st)) args} })

typeCheckDeclarations :: [FunDecl] -> Either [TCError] [FunDecl]
typeCheckDeclarations env = case execStateT (tcheckModule (reverse env)) (TCState empty empty initCtx 0) of
                              Left err -> Left [err]
                              Right s ->  Right $ updateTypes env (funcs s)

updateAss :: TySubst -> Ass -> Ass
updateAss s = M.map (map (rewrite s))


