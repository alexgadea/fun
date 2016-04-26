module Fun.Parser.Pragma where

-- Imports de parsec.
import Text.Parsec
import Text.Parsec.Token( colon, symbol, reservedOp )
import Data.Text ( Text, unpack )

-- Imports de fun.
import Fun.Parser.Internal

-- Imports de equ.
import Equ.Syntax ( Operator(..) )
import qualified Equ.Theories.FOL   as F ( theoryOperatorsList )
import qualified Equ.Theories.Arith as A ( theoryOperatorsList )

{- Ejemplo

{# AC: ≡ ∧ ∨ #}

-}

kwPragma :: ParserD ()
kwPragma = keyword "AC"

pColon :: ParserD ()
pColon = colon lexer >> return ()

pragmaBetween :: ParserD a -> ParserD a
pragmaBetween = between (symbol lexer "{#") (symbol lexer "#}") 

parsePragma :: ParserD [Operator]
parsePragma = try $ pragmaBetween pPragma

pPragma :: ParserD [Operator]
pPragma = kwPragma >> pColon >> parseOperators

operatorsList :: [Operator]
operatorsList = F.theoryOperatorsList ++ A.theoryOperatorsList

parseOperators :: ParserD [Operator]
parseOperators = many1 $ choice $ map makeOp operatorsList

makeOp :: Operator -> ParserD Operator
makeOp op = try (parseOp $ opRepr op) >> return op
    where
        parseOp :: Text -> ParserD ()
        parseOp = reservedOp lexer . unpack
