{-# Language DoAndIfThenElse,OverloadedStrings,TemplateHaskell #-}
{-| Algoritmo de chequeo e inferencia de tipos para pre-expre-
siones. Este algoritmo es esencialmente el de Hindley-Milner-Damas
para el cálculo lambda: si tenemos informacion en la pre-expresion
entonces se verifica que sea unificable con el tipo de inferido. A
diferencia de esos algoritmos, no se hay un contexto donde se declara
el tipo de las variabes, ya que la informacion de las variables
(símbolos de función y constantes son tratadas exactamente de la misma
manera) está contenida en la expresión misma (en este aspecto se
parece más al chequeo de un cálculo à la Church).
-}
module Fun.TypeChecker.Expr where

import Equ.Syntax
import Equ.PreExpr
import Equ.Types
import Equ.Theories.AbsName
import Equ.TypeChecker.Unification

import qualified Data.Map as M
import qualified Data.Text as T
import qualified Data.Set as Set (elems)
import Control.Monad.Trans.Class (lift)
import Control.Monad.Trans.State
import Control.Lens hiding (rewrite,cons)

import Control.Applicative((<$>))

-- | Ciertos s&#237;mbolos deben tener un &#250;nico tipo en toda una expresi&#243;n;
-- un contexto lleva la cuenta de todos los tipos que vamos viendo.

type CtxSyn s = M.Map s [Type]
    
-- | El contexto global es un conjunto con los contextos de cada tipo
-- de s&#237;mbolo; el contexto para los cuantificadores es fijo,
-- inicialmente tiene los cuantificadores "homog&#233;neos" (por ejemplo,
-- sumatoria est&#225;, pero forall no est&#225;).
data TCCtx = TCCtx { _vars :: CtxSyn VarName
                   , _ops  :: CtxSyn OpName 
                   , _cons :: CtxSyn ConName
                   , _quants :: CtxSyn QuantName
                   }
         deriving Show

$(makeLenses ''TCCtx)

-- | El error est&#225; acompa&#241;ado de la expresi&#243;n enfocada donde ocurri&#243;.
type TMErr = TyErr

data TCError = TCError String
             
instance Show TCError where
    show (TCError e) = e


-- | La m&#243;nada de estado del type-checker.
type TyState a = TIMonad a

type TIMonad a = StateT TCState (Either TCError) a

data TCState = TCState { _subst :: TySubst
                       , _funcs :: M.Map VarName [Type]
                       , _ctx   :: TCCtx
                       , _fTyVar :: Int
                       }

$(makeLenses ''TCState)


throwError :: String -> TIMonad a
throwError = lift . Left . TCError

-- | Generaci&#243;n de mensaje de Error.
tyerr :: TyErr -> TyState a
tyerr = throwError . show

getSub :: TyState TySubst
getSub = use subst

getCtx :: TyState TCCtx
getCtx = use ctx

getFreshTyVar :: TyState Type
getFreshTyVar = use fTyVar >>= \n -> 
                fTyVar %= (1+) >>
                return (TyVar $ T.pack (show n))

modCtx :: (TCCtx -> TCCtx) -> TyState ()
modCtx f = ctx %= f

modSubst :: (TySubst -> TySubst) -> TyState ()
modSubst f = subst %= f >> getSub >>= updateCtxS

extCtx :: (Syntactic s,Ord k) => (s -> k) -> s -> [Type] -> CtxSyn k -> CtxSyn k
extCtx f s = M.insertWith (flip const) (f s)

extCtxV :: Variable -> Type -> TyState Type
extCtxV v t = modCtx (vars %~ extCtx varName v [t]) >> return t

extCtxVar :: VarName -> Type -> TyState ()
extCtxVar v t = modCtx (vars %~ M.insertWith (flip const) v [t])

extCtxOp :: Operator -> Type -> TyState ()
extCtxOp o t = modCtx (ops %~ extCtx opName o [t])

extCtxCon :: Constant -> Type -> TyState ()
extCtxCon c t = modCtx (cons %~ extCtx conName c [t])


extCtxQuan :: Quantifier -> Type -> TyState ()
extCtxQuan q t = modCtx (quants %~ extCtx quantName q [t])


-- -- | Agrega los tipos vistos para una variable al contexto; esta funci&#243;n
-- -- se usa en el chequeo de tipos de cuantificadores.
addVar :: TCCtx -> Variable -> [Type] -> TCCtx
addVar c _ [] = c
addVar c v ts = vars %~ M.insert (tRepr v) ts $ c

-- -- | Devuelve un par con los tipos vistos de una variable y un nuevo
-- -- contexto sin esa variable.
removeVar :: TCCtx -> Variable -> (TCCtx,[Type])
removeVar c v = (vars %~ M.delete (tRepr v) $ c , M.findWithDefault [] vn vs)
    where vn = tRepr v
          vs = c ^. vars

-- | Chequeo de diferentes elementos sint&#225;cticos simples como
-- variables, constantes, s&#237;mbolos de funci&#243;n y operadores.
checkSyn :: (Ord k, Syntactic s) => s -> (s -> k) ->
            ((CtxSyn k -> Accessor (CtxSyn k) (CtxSyn k))
                -> TCCtx -> Accessor (CtxSyn k) TCCtx)
              -> TyState Type
checkSyn s name getM = use (ctx . getM) >>= withTypes s . M.lookup (name s)

errSynNoType :: (Syntactic s) => s -> TyState a
errSynNoType = tyerr . ErrNoType

withTypes :: (Syntactic s) => s -> Maybe [Type] -> TyState Type
withTypes s Nothing = errSynNoType s
withTypes s (Just []) = errSynNoType s
withTypes _ (Just ts) = rewriteS $ head ts

-- | Las diferentes instancias de checkSyn.
checkVar :: Variable -> TyState Type
checkVar v = use (ctx . vars) >>= \ct ->
             case M.lookup (varName v) ct of
               Nothing -> use funcs >>= withTypes v . M.lookup (varName v)
               Just [] -> errSynNoType v
               Just ts -> rewriteS (head ts)
               
checkCon :: Constant -> TyState Type
checkCon c = checkSyn c conName cons
checkOp :: Operator -> TyState Type
checkOp o = checkSyn o opName ops
checkQuant :: Quantifier -> TyState Type
checkQuant q = checkSyn q quantName quants

-- -- | Actualiza los tipos en el contexto.
updateCtx :: TCCtx -> TySubst -> TCCtx
updateCtx ct subs = execState (do vars %= apSubs ;
                                  ops  %= apSubs ;
                                  cons %= apSubs ) ct
          where apSubs = M.map $ map (rewrite subs)
          
updateCtxS :: TySubst -> TyState ()
updateCtxS = modCtx . flip updateCtx

-- Lifting de unificación para la mónada de TC
unifyS :: Type -> Type -> TyState TySubst
unifyS t t' = getSub >>= either tyerr (\s -> modSubst (const s) >> return s) . unify t t'

unifyListS :: [Type] -> TyState TySubst
unifyListS [] = getSub
unifyListS [_] = getSub
unifyListS (t:t':ts) = unifyS t t' >> unifyListS (t':ts)

rewriteS :: Type -> TyState Type
rewriteS t = flip rewrite t <$> getSub

updAss :: M.Map VarName [Type] -> TIMonad ()
updAss ass = getSub >>= \subs -> 
             funcs .= M.map (map (rewrite subs)) ass >>
             updateCtxS subs

updAss' :: TIMonad ()
updAss' = getSub >>= \subs -> 
          funcs %= M.map (map (rewrite subs)) >>
          updateCtxS subs

check :: PreExpr -> TyState Type
check (Var v) = checkVar v
check (Con c) = checkCon c 
check (PrExHole h) = return (tType h)
check (Paren e) = check e
check (UnOp o e) = do t  <- check e 
                      t' <- checkOp o
                      w  <- getFreshTyVar 
                      _  <- unifyS t' (t :-> w) 
                      rewriteS w
check (BinOp o e e') = do te <- check e 
                          te' <- check e'
                          tOp <- checkOp o
                          w <- getFreshTyVar
                          _ <- unifyS (te :-> te' :-> w) tOp
                          rewriteS w
check (App e e') = do te <- check e
                      te' <- check e' 
                      w <- getFreshTyVar
                      _ <- unifyS  te (te' :-> w) 
                      rewriteS w
check (Quant q v r t) = do tyQ <- checkQuant q
                           tyV <- getFreshTyVar
                           _ <- extCtxV v tyV
                           tyR <- check r
                           tyT <- check t
                           case tyQ of 
                             t1 :-> t2 -> do
                                 _ <- unifyS tyV t1
                                 _ <- unifyS t2 tyT
                                 _ <- unifyS tyR tyBool
                                 rewriteS tyT
                             t1 -> tyerr $ ErrNotExpected (tyV :-> tyT) t1
check (If b t f) = do tb <- check b
                      _ <- unifyS tb  (TyAtom ATyBool)
                      tt <- check t
                      tf <- check f
                      _ <- unifyS tt tf
                      rewriteS tt
                                     
check (Case e cs) = do texp <- check e
                       pats <- mapM checkCase cs
                       _ <- unifyListS (texp:map fst pats)
                       _ <- unifyListS (map snd pats) 
                       rewriteS (snd (head pats))


-- | Devuelve el tipo de un patrón y de la expresión.
checkCase :: (PreExpr,PreExpr) -> TyState ((Type,Type))
checkCase (p,e) = checkPat p >>= \tp ->
                  check e >>= \te -> return (tp,te)

checkPat :: PreExpr -> TyState Type
checkPat (Var v) = getFreshTyVar >>= \w -> extCtxV v w >> return w
checkPat (Con c) = checkCon c
checkPat (UnOp o e) = checkOp o >>= \t ->
                      checkPat e >>= \t'->
                      getFreshTyVar >>= \w ->
                      unifyS t (t' :-> w) >>
                      rewriteS w
checkPat (BinOp o e e') = checkOp o >>= \t ->
                          checkPat e >>= \t' ->
                          checkPat e' >>= \t'' ->
                          getFreshTyVar >>= \w ->
                          unifyS t (t' :-> t'' :-> w) >>
                          rewriteS w
checkPat (Paren p) = checkPat p
checkPat _ = error "Expression is not a pattern."

initCtx :: TCCtx
initCtx = TCCtx { _vars = M.empty
                , _ops  = M.empty
                , _cons = M.empty
                , _quants = M.empty
                }

initTCState :: TCState
initTCState = TCState { _subst = emptySubst
                      , _ctx = initCtx
                      , _fTyVar = 0
                      , _funcs = M.empty
                      }

-- | Construye un contexto con variables frescas para las variables
-- que no tienen un tipo
mkCtxVar :: PreExpr -> TyState ()
mkCtxVar e = mapM_ updCtx vs
    where vs = Set.elems $ freeVars e
          updCtx v = renTy M.empty (varTy v) >>= extCtxV v . fst

mkCtxOps :: PreExpr -> TyState ()
mkCtxOps = mapM_ updCtx . getOperators
    where updCtx o = renTy M.empty (opTy o) >>= extCtxOp o . fst

mkCtxCon :: PreExpr -> TyState ()
mkCtxCon = mapM_ updCtx . getConstants
    where updCtx con = renTy M.empty (conTy con) >>= extCtxCon con . fst

mkCtxQuan :: PreExpr -> TyState ()
mkCtxQuan = mapM_ updCtx . getQuants
    where updCtx quan = renTy M.empty (quantTy quan) >>= extCtxQuan quan . fst

-- | Dado un tipo, reemplaza todas las variables libres del
-- tipo por variables frescas.
renTy :: TySubst -> Type -> TyState (Type,TySubst)
renTy s TyUnknown = getFreshTyVar >>= \t -> return (t,s)
renTy s t@(TyAtom _) = return (t,s)
renTy s (TyVar v) = maybe newVar (\t -> return (t,s)) $ M.lookup v s
    where newVar = getFreshTyVar >>= \w ->
                   return (w, M.insert v w s)
renTy s (TyList t) = renTy s t >>= \(t',s') -> return (TyList t',s')
renTy s (t :-> t') = renTy s t >>= \(t1,s') -> 
                     renTy s' t' >>= \(t2,s'') -> return (t1 :-> t2,s'')

-- | Genera variables de tipos únicos para operadores, constantes y cuantificadores.
renTyVar :: (s -> Type) -> (s -> Type -> s) -> s -> TyState s
renTyVar acc upd s = renTy M.empty (acc s) >>= return . upd s . fst

renTyCon :: Constant -> TyState Constant
renTyCon = renTyVar conTy (\c t -> c {conTy = t})

renTyOp :: Operator -> TyState Operator
renTyOp = renTyVar opTy  (\o t -> o {opTy = t})

initCtxE :: PreExpr -> TyState ()
initCtxE e = mkCtxOps e >> mkCtxCon e >> mkCtxQuan e

mkSubst :: TCCtx -> ((Variable -> Type), (Constant -> Type), (Operator -> Type))
mkSubst (TCCtx vs os cs _) = (upd varName vs,upd conName cs,upd opName os)
    where upd field = M.foldrWithKey (\vname ty f v -> if field v == vname then head ty else f v) tyUnk
          tyUnk = const TyUnknown

setType' :: TCCtx -> PreExpr -> PreExpr
setType' ct e = setType v c o e
    where (v,c,o) = mkSubst ct

checkWithEnv :: M.Map VarName Type -> PreExpr -> TyState Type
checkWithEnv env e = initCtxE e >> mapM_ (uncurry extCtxVar) (M.toList env) >> check e

setTypeS :: PreExpr -> TyState PreExpr
setTypeS e = use ctx >>= return . flip setType' e
