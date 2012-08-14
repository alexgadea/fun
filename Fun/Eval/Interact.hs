module Fun.Eval.Interact
    ( EvResult(..)
    , errorInParsing
    , eval 
    ) where

import Text.Parsec
import Text.Parsec.String

import Lens.Family

import Equ.PreExpr(PreExpr,toExpr)
import Equ.Proof(Proof)
import Fun.Theory
import Fun.Theories(funTheory)
import Fun.Environment
import Fun.Eval.EvalMonad
import Fun.Eval.Rules hiding (getOrder,start)
import Fun.Eval.Parser
import Fun.Eval.Proof

import Control.Applicative((<$>))
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Reader
import Control.Monad

data ErrorInteract = ErrIntAlreadyRunning
                   | ErrIntNotRunning
                   | ErrIntOther String

data EvResult = EvErr ErrorInteract
              | EvOk String


instance Show ErrorInteract where
    show ErrIntAlreadyRunning = "No se puede cambiar la expresión; haga reset antes."
    show ErrIntNotRunning = "Primero se debe usar step o trace."
    show (ErrIntOther err) = "Error en un componente: " ++ err

errorInParsing = EvErr . ErrIntOther

silentOk w = liftIO . w . EvOk $ ""
resultOk w = liftIO . w . EvOk

stepPrf :: PreExpr -> EvalEnv -> IO (EvalM Proof)
stepPrf e = return . runReaderT (evalToProof e) 
            
notProgress :: (EvResult -> IO a) -> Config -> ErrorInteract -> IO (Config,Maybe Proof)
notProgress w cfg err = w (EvErr err) >> return (cfg,Nothing)

notProgress' :: (EvResult -> IO a) -> Config -> ErrorInteract -> Run Config Config
notProgress' w cfg err = liftIO (w (EvErr err)) >> return cfg


start :: EvalState -> (EvResult -> IO a) -> PreExpr -> Config -> IO (Config, Maybe Proof)
start vol w e cfg | configState cfg = stepPrf e (cfg ^. evEnv) >>=
                                      either (\err -> w (EvErr (ErrIntOther err)) >> return (cfg,Nothing)) 
                                             (\prf -> return (cfg',Just prf))
                  | otherwise       = notProgress w cfg ErrIntAlreadyRunning
    where cfg' = evState <~ vol $ (expr <~ Just e) cfg

next :: (EvResult -> IO a) -> PreExpr -> Config -> IO (Config, Maybe Proof)
next w e cfg | runningState cfg = stepPrf e (cfg ^. evEnv) >>=
                                  either (const $ w (EvErr ErrIntNotRunning) >> return (cfg,Nothing)) 
                                         (\prf -> return (cfg,Just prf))
             | otherwise        = notProgress w cfg ErrIntNotRunning

next' :: IO String -> (EvResult -> IO a) -> Run Config Config -> Run Config Config 
next' r w k = inter r w $ getCfg k >>= \cfg ->
                          listen k >>= \prf ->
                          if not (runningState cfg) 
                          then notProgress' w cfg ErrIntNotRunning
                          else getLastExpr k >>= 
                               either (notProgress' w cfg . ErrIntOther. ("Last expression"++))
                                 (\e -> 
                                 lift (lift (next w e cfg)) >>= \(c,p) -> 
                                 addProofStep c p >>= \c' ->
                                 if noisyState c'
                                 then (resultOk w . show) p >> return c'
                                 else silentOk w >> return c')

step,trace :: (EvResult -> IO a) -> PreExpr -> Config -> IO (Config,Maybe Proof)
step = start silentEval 
trace = start noisyEval

-- step' :: IO String -> (EvResult -> IO a) -> PreExpr -> Aut Config Config -> Aut Config Config
step' r w e k = advance step (\k' -> k' >>= \cfg -> silentOk w >> return cfg) r w e k
trace' r w e k = advance trace (\k' -> k' >>= \cfg -> (listen k') >>= resultOk w . show >> return cfg) r w e k

advance f k' r w e k = inter r w $ k' (k >>= (\cfg -> lift (lift (f w e cfg)) >>= uncurry addProofStep))

-- TODO: SI la expresión final de la prueba es canónica, entonces
-- pasar al estado Done.
addProofStep c = maybe (updateCfg c) (tell >=> const (updateCfg c))

updateCfg c = updCfg c >> return c

inter :: (IO String) -> (EvResult -> IO a) -> Run Config Config -> Run Config Config 
inter r w k = k >>= \cfg -> 
              liftIO r >>= \line ->
              return (parserCmd line) >>=
                     either (\err -> liftIO (w . EvErr . ErrIntOther $ err) >> return cfg)
                            (\c -> eval r w c (return cfg))

-- -- | Semántica de continuaciones para nuestro lenguaje.
eval :: IO String -> (EvResult -> IO a) -> EvCmd -> Run Config Config -> Run Config Config 
eval r w Reset = \k -> inter r w (k >> silentOk w >> resetLog >> updateCfg (initConfig []))
eval r w (Set p) = \k -> inter r w (k >>= \cfg -> silentOk w >> return (setParam p cfg))
eval r w (Step e) = step' r w e
eval r w (Trace e) = trace' r w e
eval r w (Eval e) = trace' r w e
eval r w (Get QOrder) = \k -> inter r w (k >>= liftIO . getQry (EvOk . show . getOrder) w)
eval r w (Get QInitExpr) = \k -> inter r w (k >>= liftIO . getQry (EvOk . show . getExpr) w)
eval r w (Get QCurrentProof) = \k -> inter r w (listen k >>= liftIO . w . EvOk . show >> k)
eval r w Next = next' r w



-- -- -- -- | Si hay una expresión para ser evaluada, hace n pasos
-- -- -- -- de ejecución y recolecta los resultados parciales en la lista.
-- -- -- -- Si no se puede evaluar todos los pasos, se devuelve hasta
-- -- -- -- la primera forma canónica. Satisface las siguientes reglas
-- -- -- -- @trace Nothing = trace (Just 1)@
-- -- -- -- Si @trace (Just n) = trace (Just (n+1))@, entonces
-- -- -- -- @trace (Just n) = trace (Just (n+k)@ para cualquier @k>0@.
-- -- -- -- @trace n = [] <=> not <$> canGoFurther@
-- -- -- trace :: Maybe Int -> EvalM [PreExpr]
-- -- -- trace Nothing = trace (Just 1)
-- -- -- trace (Just n) = canGoFurther >>= \canEv ->
-- -- --                  if canEv then trace' n []
-- -- --                  else return []

-- -- -- trace' :: Int -> [PreExpr] -> EvalM [PreExpr]
-- -- -- trace' 0 ps = return $ reverse ps
-- -- -- trace' n ps = getExpr >>= \(Just expr) ->
-- -- --               ask >>= \env -> 
-- -- --               case runReaderT (evalToProof expr) env of
-- -- --                 Left _ -> return []
-- -- --                 Right p -> tell p >>
-- -- --                           (toExpr <$> getEnd'' p) >>= \e ->
-- -- --                           case runReaderT (isCan e) env of
-- -- --                             Left _ -> return []
-- -- --                             Right b -> if b 
-- -- --                                       then return $ reverse (e:ps)
-- -- --                                       else put (Evaluating e) >>
-- -- --                                            trace' (n-1) (e:ps)
                             

