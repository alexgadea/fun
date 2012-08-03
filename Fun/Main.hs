{-# Language OverloadedStrings #-}
module Fun.Main where

import Fun.Environment
import Fun.Eval
import Data.Text(pack)
import Equ.Parser(parser)

import Control.Monad.RWS

main :: String -> String -> IO ()
main mod exp = loadMainModule (pack mod) >>=                
               either (error . show) 
                      (\env -> run env act >> return ())
    where exp' = parser exp
          act = setOrdNormal (
                start exp' >>
                trace (Just 10) >>= 
                liftIO . mapM_ (putStrLn . show) >> 
                return ())