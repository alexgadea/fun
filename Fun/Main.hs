{-# Language OverloadedStrings #-}
module Fun.Main where

import Fun.Environment
import Fun.Eval.Proof
import Data.Text(pack)

main :: String -> String -> IO ()
main mod exp = loadMainModule (pack mod) >>=                
               either (error . show) 
                      (putStrLn . flip testEval exp)