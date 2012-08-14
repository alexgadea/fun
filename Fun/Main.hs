{-# Language OverloadedStrings #-}
module Fun.Main where

import Fun.Environment
import Fun.Eval
import Data.Text(pack)
import Equ.Parser(parser)

import Control.Monad.RWS

main :: String -> IO ()
main mod = loadMainModule (pack mod) >>=                
           either (error . show) 
                  (\env -> getLine >>= processCommand env)