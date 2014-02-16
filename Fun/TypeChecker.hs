{-# Language TemplateHaskell,DoAndIfThenElse #-}
-- | Chequeo de tipos para un módulo. Inspirado en ``Typing Haskell in Haskell''.
module Fun.TypeChecker where

import Fun.TypeChecker.Expr
import Fun.TypeChecker.Proof
import Fun.Module
import Fun.Declarations
import Fun.Decl

import Equ.PreExpr
import Equ.Proof.Proof(Theorem(..),updThmExp,updThmPrf)
import Equ.Syntax(VarName)
import Equ.Types
import Equ.Expr (getPreExpr)
import Equ.TypeChecker.Unification

import Data.Map (Map,fromList,delete,empty)
import qualified Data.Map as M
import Control.Monad.Trans.State
import Control.Monad(replicateM)
import Control.Monad(when)
import Data.Maybe(isNothing)
import Control.Lens hiding (rewrite)
import Control.Arrow(second)

type Ass = Map VarName [Type]

tcCheckDecl :: Variable -> [Variable] -> PreExpr -> TIMonad (VarName,PreExpr)
tcCheckDecl fun args body = checkTypedDecl fun args body

checkSpecDecl :: SpecDecl -> TIMonad (VarName,PreExpr)
checkSpecDecl (Spec fun args body) = tcCheckDecl fun args body 

checkFunDecl :: FunDecl -> TIMonad (VarName,PreExpr)
checkFunDecl (Fun fun args body _) = tcCheckDecl fun args body 

checkVal :: Annot ValDecl -> TIMonad (Annot ValDecl)
checkVal (pos,(Val v expr)) = checkWithEnv M.empty expr >>= \t ->
                              getType (varTy v) >>= \t' ->
                              unifyS t t' >>
                              rewriteS t >>= \t'' ->
                              updAss' >> 
                              setTypeS expr >>= \e -> return $ (pos,Val (setVarType t'' v) e)
    where getType TyUnknown = getFreshTyVar
          getType t = return t

tcCheckProp :: Annot PropDecl -> TIMonad (Annot PropDecl)
tcCheckProp ap@(_,Prop pn expr) = mkCtxVar expr >> 
                                 checkWithEnv M.empty expr >>= \t -> 
                                 unifyS t (TyAtom ATyBool) >> 
                                 updAss' >>
                                 setTypeS expr >>= \e ->
                                 return $ second (const $ Prop pn e) ap

tcCheckThm :: Annot ThmDecl -> TIMonad (Annot ThmDecl)
tcCheckThm (pos,(Thm t e)) = mkCtxVar (getPreExpr . thExpr $ t) >>
                             checkWithEnv M.empty (getPreExpr . thExpr $ t) >>= \ty ->
                             unifyS ty (TyAtom ATyBool) >>
                             checkWithEnv M.empty e >>= \ty' ->
                             unifyS ty' (TyAtom ATyBool) >>                             
                             setTypeS (getPreExpr . thExpr $ t) >>= \e' ->
                             setTypeS e >>= \e'' ->
                             chkProof (thProof t) >>= \ p' ->
                             return (pos,Thm (updThmPrf p' (updThmExp e' t)) e'')

checkDeriv :: DerivDecl -> TIMonad ()
checkDeriv (Deriv _ _ _) = return ()

checkTypedDecl :: Variable -> [Variable] -> PreExpr -> TIMonad (VarName,PreExpr)
checkTypedDecl fun args body = do ass <- use funcs
                                  let t = M.lookup (varName fun) ass 
                                  when (isNothing t) (throwError $ "Función que no está en la lista de suposiciones")
                                  let (Just ts) = t
                                  when (null ts) (throwError $ "Función que está en la lista, sin tipo!")
                                  let ty = head ts
                                  if arity ty /= length args
                                  then throwError $ "Unexpected number of arguments: " ++ show ty ++ " <> " ++ show args
                                  else do 
                                    let argsTy = argsTypes ty
                                    let varsTy = fromList $ (varName fun,ty): zipWith (\v t' -> (varName v,t')) args argsTy
                                    ty' <- checkWithEnv varsTy body
                                    _ <- unifyS ty (exponential ty' argsTy)
                                    body' <- setTypeS body
                                    _ <- localState args
                                    ass' <- use (ctx . vars)
                                    _ <- updAss (M.union ass ass')
                                    return (varName fun,body')

addAssumption :: (Variable,[Variable]) -> TIMonad ()
addAssumption (f,args) = use funcs >>= \ass ->
                         if varTy f /= TyUnknown
                         then updAss $ M.insert (varName f) [varTy f] ass
                         else replicateM (length args) getFreshTyVar >>= \ts ->
                              getFreshTyVar >>= \tr ->
                              updAss $ M.insert (varName f) [exponential tr ts] ass

tcCheckModule :: Module -> [(VarName,[Type])] -> TIMonad Module
tcCheckModule m a = do let dcls = m ^. validDecls
                       let fs   = bare functions dcls
                       let sps  = bare specs dcls
                       let vls  = dcls ^. vals 
                       let thms = dcls ^. theorems
                       let prps = dcls ^. props
                       let env  = map (\f -> (f ^. funDeclName,f ^. funDeclArgs)) fs
                               ++ map (\f -> (f ^. specName,f ^. specArgs)) sps

                       updAss (M.fromList a)
                       mapM_ addAssumption env

                       fbds <- mapM checkFunDecl fs
                       sbds <- mapM checkSpecDecl sps
                       vls' <- mapM checkVal vls
                       thms' <- mapM tcCheckThm thms
                       prps' <- mapM tcCheckProp prps

                       env' <- use funcs 

                       return $ execState (do validDecls . functions %= updFunTypes fbds env' ;
                                              validDecls . specs  %= updSpecTypes sbds env'    ;
                                              validDecls . vals  .= vls'                     ;
                                              validDecls . theorems .= thms';
                                              validDecls . props .= prps';
                                            ) m

updFunTypes :: [(VarName,PreExpr)] -> Ass -> [Annot FunDecl] -> [Annot FunDecl]
updFunTypes bds ass fs = map updDecl fs
    where updDecl f = maybe f (flip (changeTypeDecl bd) f . head) $ M.lookup fname ass
              where fname = f ^. _2 ^. funDeclName ^. to varName
                    bd = lookup fname bds

updSpecTypes :: [(VarName,PreExpr)] -> Ass -> [Annot SpecDecl] -> [Annot SpecDecl]
updSpecTypes bds ass fs = map updDecl fs
    where updDecl f = maybe f (flip (changeSpecType bd) f . head) $ M.lookup fname ass
              where fname = f ^. _2 ^. specName ^. to varName
                    bd = lookup fname bds


setVarType :: Type -> Variable -> Variable
setVarType t v = v { varTy = t}

changeTypeDecl :: Maybe PreExpr -> Type -> Annot FunDecl -> Annot FunDecl
changeTypeDecl e ty = second $ (funDeclName %~ setVarType ty) . 
                                 (funDeclArgs %~ (zipWith setVarType (argsTypes ty))) .
                                 (funDeclBody %~ maybe id (\x -> const x) e)

changeSpecType :: Maybe PreExpr -> Type -> Annot SpecDecl -> Annot SpecDecl
changeSpecType e ty = second $ (specName %~ setVarType ty) .
                                 (specArgs %~ (zipWith setVarType (argsTypes ty))) .
                                 (specSpec %~ maybe id (\x -> const x) e)


withoutLocal :: Ass -> [Variable] -> Ass
withoutLocal = foldr (delete . varName)

localState :: [Variable] -> TIMonad ()
localState args = ctx . vars %= flip withoutLocal args

typeCheckDeclarations :: Module -> [(VarName,[Type])] -> Either String Module
typeCheckDeclarations m ass = case runStateT (tcCheckModule m ass) (TCState empty empty initCtx 0) of
                                Left (TCError err) -> Left $ err
                                Right (m',_) ->  Right m' -- updateTypes env (s ^. funcs)

updateAss :: TySubst -> Ass -> Ass
updateAss s = M.map (map (rewrite s))
