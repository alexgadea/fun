module Fun.Eval.Parser where

import Text.Parsec
import Text.Parsec.String

import Fun.Environment
import Fun.Eval.EvalMonad
import Fun.Eval.Rules(EvOrder(..))
import Equ.PreExpr(PreExpr)
import Equ.Parser

import Data.Functor.Identity

import Control.Applicative hiding (many)

type ParserCmd b = ParsecT String PExprState Identity b

envQP,orderQP,proofQP,exprQP,lastQP,stateQP :: ParserCmd Query
orderQP = QOrder <$ string "order"
proofQP = QCurrentProof <$ string "proof"
envQP = QCurrentEnv <$ string "env"
exprQP = QInitExpr <$ string "expr"
lastQP = QLastResult <$ string "result"
stateQP = QState <$ string "state"

queriesP = choice . map try $ [ orderQP
                              , proofQP
                              , exprQP
                              , lastQP
                              , envQP
                              , stateQP
                              ]

queryP :: ParserCmd EvCmd
queryP = Get <$> (string "get" *> blanks *> queriesP)


stepP,traceP,evalP,showP :: ParserCmd EvCmd
stepP = Step <$> (string "step" *> blanks *> parsePreExpr)
traceP = Trace <$> (string "trace" *> blanks *> parsePreExpr)
evalP = Eval <$> (string "eval" *> blanks *> parsePreExpr)
showP = Show <$> (string "show" *> blanks *> parsePreExpr)

helpP,nextP,resetP :: ParserCmd EvCmd
nextP = Next <$ string "next"
resetP = Reset <$ string "reset"
helpP = Help <$ string "help"

setOrder :: ParserCmd EvCmd
setOrder = Set . Order <$> (string ":set" *> blanks *> evOrder)
    where evOrder :: ParserCmd EvOrder
          evOrder = choice [ try $ Eager <$ string "eager"
                           , try $ Normal <$  string "normal"
                           ]

withNumArg :: ParserCmd String -> ParserCmd (String,Int)
withNumArg p = p >>= \cmd -> blanks >> 
               many1 digit >>= \ds -> return (cmd,num 0 ds)
    where num ac [] = ac
          num ac (n:ns) = num (ac*10+(read [n])) ns

blanks = many1 $ oneOf "\r\t "

evalParser :: ParserCmd EvCmd
evalParser = choice $ map try [ nextP
                              , resetP
                              , setOrder
                              , stepP
                              , showP
                              , traceP
                              , evalP
                              , queryP 
                              , helpP ]


parserCmd :: String -> Either String EvCmd
parserCmd = either (Left . show) Right . runParser evalParser (initPExprState UnusedParen) "EvalCommand"
    where cmd acc  = either (Left . show) (Right . acc) . parseFromString 
