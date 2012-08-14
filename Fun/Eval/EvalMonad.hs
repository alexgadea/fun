{-# Language TemplateHaskell #-}
module Fun.Eval.EvalMonad where

import Lens.Family
import Lens.Family.TH

import Equ.PreExpr(PreExpr,toExpr)
import Equ.Proof(Proof)
import Fun.Theory
import Fun.Theories(funTheory)
import Fun.Environment
import Fun.Eval.Rules hiding (start)
import Fun.Eval.Proof

import Data.Monoid

import Control.Applicative((<$>))
import Control.Monad.IO.Class
import Control.Monad.Trans.Class
import Control.Monad.Trans.State
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Cont

import Control.Arrow


data EvRunType = Silent -- ^ No se muestra el resultado en cada paso.
               | Noisy  -- ^ Se muestra el resultado en cada paso.
                 deriving Show

data EvalState = Init 
               | Evaluating EvRunType
               | Done
                 deriving Show

-- | Parámetros para la evaluación.
data Param = Order EvOrder

noisyEval = Evaluating Noisy
silentEval = Evaluating Silent

data Config = Config { 
      _evState :: EvalState
    , _evEnv :: EvalEnv
    , _expr :: Maybe PreExpr
    }

$(mkLenses ''Config)


data Query = QOrder
           | QCurrentProof
           | QInitExpr
           | QLastResult
             
-- | Comandos para la máquina de estados de la consola de
-- evaluación
data EvCmd = Reset         -- ^ Descarta cualquier evaluación que se estuviera haciendo.
           | Set Param     -- ^ Setea parámetros para la evaluación.
           | Trace PreExpr -- ^ Comienza la evaluación paso por paso, mostrando cada resultado
                           -- parcial.
           | Step  PreExpr -- ^ Como trace pero sólo muestra la forma canónica.
           | Eval  PreExpr -- ^ Como step pero realiza todos los pasos.
           | Next          -- ^ Continúa la evaluación comenzada por trace o step.
           | Get Query


-- | La evaluación está estructurada con continuaciones.
type Run r a = ContT r Aut a
type Aut = StateT (Config,Proof) IO

initConfig :: Environment -> Config
initConfig en = Config Init initEnv Nothing
    where initEnv = EvalEnv Eager (Env $ getFuncs en) funTheory


running :: EvalState -> Bool
running (Evaluating _) = True
running _ = False

-- | Estamos haciendo ruido?
noisy :: EvalState -> Bool
noisy (Evaluating Noisy) = True
noisy _ = False

-- | Configurable?
configurable :: EvalState -> Bool
configurable Init = True
configurable _ = False


noisyState :: Config -> Bool
noisyState cfg = noisy $ cfg ^. evState

configState :: Config -> Bool
configState cfg = configurable $ cfg ^. evState

runningState :: Config -> Bool
runningState cfg = running $ cfg ^. evState

setParam :: Param -> Config -> Config
setParam (Order o) cfg = if configState cfg
                         then (evEnv ^= (order ^= o) (cfg ^. evEnv)) cfg
                         else cfg

getOrder :: Config -> EvOrder
getOrder cfg = cfg ^. (evEnv . order)

getExpr :: Config -> Maybe PreExpr
getExpr cfg = cfg ^. expr

getQry :: (Config -> a) -> (a -> IO b) -> Config -> IO Config
getQry q p cfg = (p . q) cfg >> return cfg

getInitExpr :: Run r a -> Run r (Maybe PreExpr)
getInitExpr k = k >>= \_ -> (getExpr . fst <$> lift get)

listen :: Run r a -> Run r Proof
listen k = k >> snd <$> lift get

tell :: Proof -> Run r ()
tell p = lift (modify (second (\p' -> p' `mappend` p)))

resetLog :: Run r ()
resetLog = lift (modify (second (const mempty)))



getLastExpr :: Run r a -> Run r (Either String PreExpr)
getLastExpr k = listen k >>= \prf -> 
                getCfg k >>= \cfg -> 
                return (runReaderT (getEnd'' prf) (cfg ^. evEnv))

updCfg :: Config -> Run r ()
updCfg cfg = lift (modify (first (const cfg)))

getCfg :: Run r a -> Run r Config
getCfg k = k >> fst <$> lift get