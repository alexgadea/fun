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

orderQP,proofQP,exprQP,lastQP :: ParserCmd Query
orderQP = QOrder <$ string "order"
proofQP = QCurrentProof <$ string "proof"
exprQP = QInitExpr <$ string "expr"
lastQP = QLastResult <$ string "result"

queriesP = choice . map try $ [ orderQP
                              , proofQP
                              , exprQP
                              , lastQP
                              ]

queryP :: ParserCmd EvCmd
queryP = Get <$> (string "get" *> blanks *> queriesP)


stepP,traceP,evalP :: ParserCmd EvCmd
stepP = Step <$> (string "step" *> blanks *> parsePreExpr)
traceP = Trace <$> (string "trace" *> blanks *> parsePreExpr)
evalP = Eval <$> (string "eval" *> blanks *> parsePreExpr)

nextP,resetP :: ParserCmd EvCmd
nextP = Next <$ string "next"
resetP = Reset <$ string "reset"

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

blanks = many1 (oneOf "\r\t ")

evalParser :: ParserCmd EvCmd
evalParser = choice [ try nextP
                    , try resetP
                    , try setOrder
                    , try stepP
                    , try traceP
                    , try evalP
                    , try queryP ]


parserCmd :: String -> Either String EvCmd
parserCmd = either (Left . show) Right . runParser evalParser (initPExprState UnusedParen) "EvalCommand"
    where cmd acc  = either (Left . show) (Right . acc) . parseFromString 
