module Fun.Eval.Parser where

import Text.Parsec
import Text.Parsec.String

import Fun.Environment
import Fun.Eval.EvalMonad
import Fun.Eval.Rules(EvOrder(..))
import Equ.PreExpr(PreExpr)
import Equ.Parser(parseFromString)

import Control.Applicative hiding (many)

orderQP,proofQP,exprQP,lastQP :: Parser Query
orderQP = QOrder <$ string "order"
proofQP = QCurrentProof <$ string "proof"
exprQP = QInitExpr <$ string "expr"
lastQP = QLastResult <$ string "result"

queriesP = choice . map try $ [ orderQP
                              , proofQP
                              , exprQP
                              , lastQP
                              ]

queryP :: Parser (PreExpr -> EvCmd)
queryP = (Get <$> (string "get" *> blanks *> queriesP)) >>= return . const


stepP,traceP,evalP :: Parser (PreExpr -> EvCmd)
stepP = Step <$ string "step"
traceP = Trace <$ string "trace"
evalP = Eval <$ string "eval" 

nextP,resetP :: Parser (PreExpr -> EvCmd)
nextP = const Next <$ withNumArg (string "next") 
resetP = const Reset <$ (string "reset")

setOrder :: Parser (PreExpr -> EvCmd)
setOrder = Set . Order <$> (string ":set" *> blanks *> evOrder) >>= 
           return . const
    where evOrder :: Parser EvOrder
          evOrder = choice [ try $ Eager <$ string "eager"
                           , try $ Normal <$  string "normal"
                           ]

withNumArg :: Parser String -> Parser (String,Int)
withNumArg p = p >>= \cmd -> blanks >> 
               many1 digit >>= \ds -> return (cmd,num 0 ds)
    where num ac [] = ac
          num ac (n:ns) = num (ac*10+(read [n])) ns

blanks = many1 (oneOf "\r\t ")

evalParser :: Parser (PreExpr -> EvCmd,String)
evalParser = choice [ try nextP
                    , try resetP
                    , try setOrder
                    , try stepP
                    , try traceP
                    , try evalP
                    , try queryP ] >>= 
             \ac -> blanks >> many anyChar >>= \str -> 
             return (ac,str)


parserCmd :: String -> Either String EvCmd
parserCmd = either (Left . show) (uncurry cmd) . runParser evalParser () "EvalCommand"
    where cmd acc  = either (Left . show) (Right . acc) . parseFromString 
