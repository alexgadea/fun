module Fun.Eval where

import Fun.Eval.EvalMonad
import Fun.Eval.Interact
import Fun.Eval.Parser
import Fun.Eval.Rules hiding (EvalM,start)
import Fun.Eval.Proof
import Fun.Theory
import Fun.Theories(funTheory)
import Fun.Environment

import Equ.Parser
import Equ.PreExpr(PreExpr,toExpr)
import Equ.Proof(Proof)

import Control.Applicative((<$>))
<<<<<<< Updated upstream
import Control.Monad.Trans.Writer
import Control.Monad.Trans.State
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Cont
import Data.Monoid
=======
import Control.Monad.RWS 
import Control.Monad.Reader

data EvalState = Prepared
               | Evaluating PreExpr
               | Done PreExpr

initEnv en = EvalEnv Eager (Env $ getFuncs en) funTheory

isDone :: EvalState -> Bool
isDone st | Done _ <- st = True
          | otherwise = False

isEval :: EvalState -> Bool
isEval st | Evaluating _ <- st = True
          | otherwise    = False

canConfig :: EvalState -> Bool
canConfig st = not (isEval st && isDone st)

type EvalM = RWST EvalEnv Proof EvalState IO

run :: Environment -> EvalM a -> IO (a,EvalState,Proof)
run env m = runRWST m (initEnv env) Prepared 

-- | Devuelve la expresión que se está evaluando.
getExpr' :: EvalState -> Maybe PreExpr
getExpr' Prepared = Nothing
getExpr' (Evaluating e) = Just e
getExpr' (Done e) = Just e

getExpr :: EvalM (Maybe PreExpr)
getExpr = gets getExpr'
                        
finished :: EvalM Bool
finished = gets isDone

new :: EvalM ()
new = put Prepared

set :: (EvalEnv -> EvalEnv) -> EvalM a -> EvalM ()
set f m = gets canConfig >>= \conf -> 
          when conf (local f m >> return ())

-- | Define qué funciones existen
setEnv :: Env -> EvalM () -> EvalM ()
setEnv e = set ((<~) env e)

-- | Define qué teorías se usan
setThs :: [Theory] -> EvalM () -> EvalM ()
setThs ths = set ((<~) theories ths)

-- | Se usará el orden correspondiente
setOrdNormal :: EvalM () -> EvalM ()
setOrdNormal = set ((<~) order Normal)

setOrdEager :: EvalM () -> EvalM ()
setOrdEager  = set ((<~) order Eager) 

-- | Pone una expresión para ser evaluada, pero no la evaluá.
-- Una vez que se usa @start@ las funciones de más arriba
-- no tienen ningún efecto, hasta que se use @clear@.
start :: PreExpr -> EvalM ()
start e  = get >>= \s -> case s of
                          Prepared -> put $ Evaluating e
                          Done _ -> return ()
                          Evaluating _ -> put $ Evaluating e

-- | Descarta la expresión a ser evaluada, si es que hay alguna.
clear :: EvalM ()
clear  = new

-- | Si hay una expresión para ser evaluada, hace n pasos
-- de ejecución y recolecta los resultados parciales en la lista.
-- Si no se puede evaluar todos los pasos, se devuelve hasta
-- la primera forma canónica. Satisface las siguientes reglas
-- @trace Nothing = trace (Just 1)@
-- Si @trace (Just n) = trace (Just (n+1))@, entonces
-- @trace (Just n) = trace (Just (n+k)@ para cualquier @k>0@.
-- @trace n = [] <=> not <$> canGoFurther@
trace :: Maybe Int -> EvalM [PreExpr]
trace Nothing = trace (Just 1)
trace (Just n) = canGoFurther >>= \canEv ->
                 if canEv then trace' n []
                 else return []

trace' :: Int -> [PreExpr] -> EvalM [PreExpr]
trace' 0 ps = return $ reverse ps
trace' n ps = getExpr >>= \(Just expr) ->
              ask >>= \env -> 
              case runReaderT (evalToProof expr) env of
                Left _ -> return []
                Right p -> tell p >>
                          (toExpr <$> getEnd'' p) >>= \e ->
                          case runReaderT (isCan e) env of
                            Left _ -> return []
                            Right b -> if b 
                                      then return $ reverse (e:ps)
                                      else put (Evaluating e) >>
                                           trace' (n-1) (e:ps)
                             


-- | Como @trace@ pero se queda con el último resultado.
step :: Maybe Int -> EvalM (Maybe PreExpr)
step n = last' <$> trace n
    where last' xs = if null xs then Nothing else Just $ last xs
>>>>>>> Stashed changes

import Text.Parsec

run env cmd = runStateT (runContT (eval getLine putStrLn cmd (return cfg)) return) (cfg,mempty)
    where cfg = initConfig env

processCommand :: Environment -> String -> IO ()
processCommand env = either putStrLn doEv . parserCmd
    where doEv cmd = run env cmd >> return ()
