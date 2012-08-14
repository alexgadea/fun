module Fun.Eval.Interact where

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

instance Show ErrorInteract where
    show ErrIntAlreadyRunning = "No se puede cambiar la expresión; haga reset antes."
    show ErrIntNotRunning = "Primero se debe usar step o trace."

stepPrf :: PreExpr -> EvalEnv -> IO (EvalM Proof)
stepPrf e = return . runReaderT (evalToProof e) 
            
notProgress :: (String -> IO a) -> Config -> ErrorInteract -> IO (Config,Maybe Proof)
notProgress w cfg err = w (show err) >> return (cfg,Nothing)


start :: EvalState -> (String -> IO a) -> PreExpr -> Config -> IO (Config, Maybe Proof)
start vol w e cfg | configState cfg = stepPrf e (cfg ^. evEnv) >>=
                                      either (\err -> w err >> return (cfg,Nothing)) 
                                             (\prf -> return (cfg',Just prf))
                  | otherwise       = notProgress w cfg ErrIntAlreadyRunning
    where cfg' = evState ^= vol $ (expr ^= Just e) cfg

next :: (String -> IO a) -> PreExpr -> Config -> IO (Config, Maybe Proof)
next w e cfg | runningState cfg = stepPrf e (cfg ^. evEnv) >>=
                                  either (const $ return (cfg,Nothing)) 
                                         (\prf -> return (cfg,Just prf))
             | otherwise        = notProgress w cfg ErrIntNotRunning

next' :: IO String -> (String -> IO ()) -> Run Config Config -> Run Config Config 
next' r w k = inter r w $ (getCfg k >>= \cfg ->
                           listen k >>= \prf ->
                           getLastExpr k >>= \e ->
                           lift (lift (next w e cfg)) >>= \(c,p) -> 
                           addProofStep c p >>= \c' ->
                           if noisyState c'
                           then (liftIO . w . show) p >> return c'
                           else (liftIO $ w "") >> return c')

step,trace :: (String -> IO ()) -> PreExpr -> Config -> IO (Config,Maybe Proof)
step = start silentEval 
trace = start noisyEval

-- step' :: IO String -> (String -> IO ()) -> PreExpr -> Aut Config Config -> Aut Config Config
step' r w e k = advance step (\k' -> k' >>= \cfg -> liftIO (w (show "")) >> return cfg) r w e k
trace' r w e k = advance trace (\k' -> k' >>= \cfg -> (listen k') >>= liftIO . w . show >> return cfg) r w e k

advance f k' r w e k = inter r w $ k' (k >>= (\cfg -> lift (lift (f w e cfg)) >>= uncurry addProofStep))

-- TODO: SI la expresión final de la prueba es canónica, entonces
-- pasar al estado Done.
addProofStep c = maybe updateCfg (tell >=> const updateCfg)
    where updateCfg = updCfg c >> return c

inter :: (IO String) -> (String -> IO ()) -> Run Config Config -> Run Config Config 
inter r w k = k >>= \cfg -> 
              liftIO r >>= \line ->
              return (parserCmd line) >>=
                     either (\err -> liftIO (w err) >> return cfg)
                            (\c -> eval r w c (return cfg))

-- -- | Semántica de continuaciones para nuestro lenguaje.
eval :: IO String -> (String -> IO ()) -> EvCmd -> Run Config Config -> Run Config Config 
eval r w Reset = \k -> inter r w (k >>= return . const (initConfig []))
eval r w (Set p) = \k -> inter r w (k >>= return . setParam p)
eval r w (Step e) = step' r w e
eval r w (Trace e) = trace' r w e
eval r w (Eval e) = trace' r w e
eval r w (Get QOrder) = \k -> inter r w (k >>= liftIO . getQry (show . getOrder) w)
eval r w (Get QInitExpr) = \k -> inter r w (k >>= liftIO . getQry (show . getExpr) w)
eval r w (Get QCurrentProof) = \k -> inter r w (listen k >>= liftIO . w . show >> k)
eval r w Next = next' r w


-- -- -- run :: Environment -> EvalM a -> IO (a,EvalState,Proof)
-- -- -- run env m = runRWST m (initEnv env) Init 

-- -- -- getExpr :: EvalM (Maybe PreExpr)
-- -- -- getExpr = gets getExpr'
                        
-- -- -- finished :: EvalM Bool
-- -- -- finished = gets isDone

-- -- -- new :: EvalM ()
-- -- -- new = put Init

-- -- -- set :: (EvalEnv -> EvalEnv) -> EvalM a -> EvalM ()
-- -- -- set f m = gets canConfig >>= \conf -> 
-- -- --           when conf (local f m >> return ())

-- -- -- -- | Define qué funciones existen
-- -- -- setEnv :: Env -> EvalM () -> EvalM ()
-- -- -- setEnv e = set ((^=) env e)

-- -- -- -- | Define qué teorías se usan
-- -- -- setThs :: [Theory] -> EvalM () -> EvalM ()
-- -- -- setThs ths = set ((^=) theories ths)

-- -- -- -- | Se usará el orden correspondiente
-- -- -- setOrdNormal :: EvalM () -> EvalM ()
-- -- -- setOrdNormal = set ((^=) order Normal)

-- -- -- setOrdEager :: EvalM () -> EvalM ()
-- -- -- setOrdEager  = set ((^=) order Eager) 

-- -- -- -- | Pone una expresión para ser evaluada, pero no la evaluá.
-- -- -- -- Una vez que se usa @start@ las funciones de más arriba
-- -- -- -- no tienen ningún efecto, hasta que se use @clear@.
-- -- -- start :: PreExpr -> EvalM ()
-- -- -- start e  = get >>= \s -> case s of
-- -- --                           Init -> put $ Evaluating e
-- -- --                           Done _ -> return ()
-- -- --                           Evaluating _ -> put $ Evaluating e

-- -- -- -- | Descarta la expresión a ser evaluada, si es que hay alguna.
-- -- -- clear :: EvalM ()
-- -- -- clear  = new

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
                             


-- -- -- -- | Como @trace@ pero se queda con el último resultado.
-- -- -- step :: Maybe Int -> EvalM (Maybe PreExpr)
-- -- -- step n = last' <$> trace n
-- -- --     where last' xs = if null xs then Nothing else Just $ last xs

-- -- -- -- | Determina si puede evaluarse un paso más.
-- -- -- -- @start e >>= canGoFurther >>= liftM (==True)@
-- -- -- -- sii @not (isCanonical e)@.
-- -- -- canGoFurther :: EvalM Bool
-- -- -- canGoFurther = gets isEval

-- -- -- data EvResult = EvErr String
-- -- --               | EvOk [PreExpr]


-- -- -- fmtEvResult :: EvResult -> String
-- -- -- fmtEvResult (EvErr err) = err
-- -- -- fmtEvResult (EvOk es) = fmtExps es

-- -- -- fmtExps :: [PreExpr] -> String
-- -- -- fmtExps [] = ""
-- -- -- fmtExps [e] = show e
-- -- -- fmtExps es = unlines $ zipWith fmtExp [1..] es
-- -- --     where fmtExp n = (show n++) . showExp'

-- -- -- showExp' :: PreExpr -> String
-- -- -- showExp' = unlines . map (\l -> "\t"++l) . lines . show


-- -- -- showError :: String -> String -> EvResult
-- -- -- showError mom err = EvErr $ unlines [ mom ++ ": ", "\t" ++ err]

-- -- -- runCmd :: EvAction -> PreExpr -> EvalM EvResult
-- -- -- runCmd (Step n) e = start e >>
-- -- --                     step (Just n) >>=
-- -- --                     return . maybe (EvErr "No se pudo evaluar la expresión") (EvOk . return)
-- -- -- runCmd (Trace n) e = start e >>
-- -- --                      trace (Just n) >>= \es ->
-- -- --                      return $ if null es
-- -- --                               then EvErr "No se pudo evaluar la expresión"
-- -- --                               else EvOk es
-- -- -- runCmd Eval _ = return $ EvErr "Comando no implementado"
-- -- -- runCmd (Set _) _ = return $ EvErr "Comando no implementado"
