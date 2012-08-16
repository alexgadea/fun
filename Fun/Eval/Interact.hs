module Fun.Eval.Interact
    ( EvResult(..)
    , parserCmdCont
    , eval 
    ) where

import Text.Parsec
import Text.Parsec.String

import Lens.Family

import Equ.PreExpr(PreExpr,toExpr,toFocus)
import Equ.Proof(Proof,getEnd)

import Fun.Theory
import Fun.Theories(funTheory)
import Fun.Environment
import Fun.Eval.EvalMonad
import Fun.Eval.Rules hiding (getOrder,start,getEnv)
import Fun.Eval.Parser
import Fun.Eval.Help
import Fun.Eval.Proof

import Control.Applicative((<$>))
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.Cont
import Control.Monad.Trans.Reader
import Control.Monad

type Interact a b = IO String -> (EvResult -> IO a) -> b

data ErrorInteract = ErrIntAlreadyRunning
                   | ErrIntNotRunning
                   | ErrIntOther String

data EvResult = EvErr ErrorInteract
              | EvOk String


instance Show ErrorInteract where
    show ErrIntAlreadyRunning = "No se puede cambiar la expresión; haga reset antes."
    show ErrIntNotRunning = "Primero se debe usar step o trace."
    show (ErrIntOther err) = "Error en un componente: " ++ err

errorInOther = EvErr . ErrIntOther

silentOk w = liftIO . w . EvOk $ ""
resultOk w = liftIO . w . EvOk

stepPrf :: PreExpr -> EvalEnv -> IO (EvalM Proof)
stepPrf e = return . runReaderT (evalToProof e) 

evalPrf :: PreExpr -> EvalEnv -> IO (EvalM Proof)
evalPrf e = return . runReaderT (evalF (toFocus e))
            
notProgress :: (EvResult -> IO a) -> Config -> ErrorInteract -> IO (Config,Maybe Proof)
notProgress w cfg err = w (EvErr err) >> return (cfg,Nothing)

notProgress' :: (EvResult -> IO a) -> Config -> ErrorInteract -> Run Config Config
notProgress' w cfg err = liftIO (w (EvErr err)) >> return cfg


start :: (PreExpr -> EvalEnv -> IO (EvalM Proof)) -> EvalState -> (EvResult -> IO a) -> 
        PreExpr -> Config -> IO (Config, Maybe Proof)
start f vol w e cfg | configState cfg = f e (cfg ^. evEnv) >>=
                                        either (\err -> w (EvErr (ErrIntOther err)) >> return (cfg,Nothing)) 
                                               (\prf -> return (done prf cfg',Just prf))
                    | otherwise       = notProgress w cfg ErrIntAlreadyRunning
    where cfg' = evState <~ vol $ (expr <~ Just e) cfg

next :: (EvResult -> IO a) -> PreExpr -> Config -> IO (Config, Maybe Proof)
next w e cfg | runningState cfg = stepPrf e (cfg ^. evEnv) >>=
                                  either (const $ w (EvErr ErrIntNotRunning) >> return (cfg,Nothing)) 
                                         (\prf -> return (done prf cfg,Just prf))
             | otherwise        = notProgress w cfg ErrIntNotRunning

done :: Proof -> Config -> Config
done p cfg = if proofDone p (cfg ^. evEnv)
             then (evState <~ Done) cfg 
             else cfg

next' :: Interact a (Run Config Config -> Run Config Config)
next' r w k = inter r w $ k >> getCfg >>= \cfg ->
                          listen >>= \prf ->
                          if not (runningState cfg) 
                          then notProgress' w cfg ErrIntNotRunning
                          else getLastExpr >>= 
                               either (notProgress' w cfg . ErrIntOther. ("Last expression"++))
                                 (\e -> 
                                 lift (lift (next w e cfg)) >>= \(c,p) -> 
                                 addProofStep c p >>= \c' ->
                                 if noisyState c'
                                 then (resultOk w . show) p >> return c'
                                 else silentOk w >> return c')

step,trace :: (EvResult -> IO a) -> PreExpr -> Config -> IO (Config,Maybe Proof)
step = start stepPrf silentEval 
trace = start stepPrf noisyEval
evalCmd = start evalPrf noisyEval 

step',trace',evalCmd'  :: Interact a (PreExpr -> Run Config Config -> Run Config Config)
step' r w = advance step (silentOk w) r w 
trace' r w = advance trace (listen >>= resultOk w . show) r w 
evalCmd' r w = advance evalCmd result r w
    where result = listen >>=
                   either (liftIO . w . errorInOther . show)
                          (resultOk w . show . toExpr) 
                          . getEnd

advance :: ((EvResult -> IO a) -> PreExpr -> Config -> IO (Config, Maybe Proof))
        -> Run Config b -> Interact a (PreExpr -> Run Config Config -> Run Config Config)
advance f k' r w e = inter r w . withCont' (lift . lift . f w e >=>
                                            uncurry addProofStep >=> 
                                            const k')

addProofStep :: Config -> Maybe Proof -> Run a Config
addProofStep c = maybe (updateCfg c) (\p -> tell p >> updateCfg (done p c))
    where updateCfg c = updCfg c >> return c

withCont' :: (Config -> Run Config a) -> Run Config Config -> Run Config Config
withCont' k' k = k >>= \cfg -> k' cfg >> return cfg

inter :: (IO String) -> (EvResult -> IO a) -> Run Config Config -> Run Config Config 
inter r w = withCont' (\cfg -> liftIO r >>= parserCmdCont r w cfg)

parserCmdCont :: (IO String) -> (EvResult -> IO a) -> Config -> String -> Run Config Config
parserCmdCont r w cfg = either (liftIO . w . EvErr . ErrIntOther >=> const (return cfg))
                            (\cmd -> eval r w cmd (return cfg)) . parserCmd 

-- -- | Semántica de continuaciones para nuestro lenguaje.
eval :: IO String -> (EvResult -> IO a) -> EvCmd -> Run Config Config -> Run Config Config 
eval r w Reset = withCont' (const $ silentOk w)
eval r w (Set p) = inter r w . (withCont' (\cfg -> silentOk w >> return (setParam p cfg)))
eval r w (Step e) = step' r w e
eval r w (Trace e) = trace' r w e
eval r w (Eval e) = evalCmd' r w e
eval r w Next = next' r w
eval r w (Get q) = inter r w . withCont' (evalQ w q)
eval r w (Show e) = inter r w . withCont'  (const $ resultOk w . show $ e)
eval r w Help = inter r w . withCont' (const $ resultOk w . show $ Help)

evalQ :: (EvResult -> IO a) -> Query -> Config -> Run Config a
evalQ w q cfg = listen >>= liftIO . w . evalQry q cfg

evalQry :: Query -> Config -> Proof -> EvResult
evalQry QOrder cfg _ = EvOk $ show $ getOrder cfg
evalQry QInitExpr cfg _ = EvOk $  show $ getExpr cfg
evalQry QCurrentProof _ prf = EvOk $ show prf
evalQry QCurrentEnv cfg _ = EvOk $ show $ getEnv cfg
evalQry QState cfg _ = EvOk $ show $ cfg ^. evState
evalQry QLastResult _ prf = either (errorInOther . ("QLastResult: "++) . show) (EvOk . show) $ getEnd prf