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
import Control.Monad.Trans.Writer
import Control.Monad.Trans.State
import Control.Monad.Trans.Reader
import Control.Monad.Trans.Cont
import Data.Monoid

import Text.Parsec

run env cmd = runStateT (runContT (eval getLine putStrLn cmd (return cfg)) return) (cfg,mempty)
    where cfg = initConfig env

processCommand :: Environment -> String -> IO ()
processCommand env = either putStrLn doEv . parserCmd
    where doEv cmd = run env cmd >> return ()
