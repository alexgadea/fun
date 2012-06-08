-- | Modulo que define el tipos de estado para el parser de fun.
module Fun.Parser.Internal where

-- Imports Parsec
import Text.Parsec 
import Text.Parsec.Token
import Text.Parsec.Language

-- Imports Monad.
import Control.Monad.Identity (Identity)

-- Imports Data.*
import qualified Data.Map as M (Map)

-- Imports Equ.
import Equ.Types(Type)
import Equ.Syntax(VarName,FuncName)

-- Imports Fun.
import Fun.Environment

type EitherName = Either VarName FuncName

type VarTy = (Int,M.Map EitherName Type)

data PState = PState { pEnv :: Environment
                     , pVarTy :: VarTy
                     }

type ParserD a = ParsecT String PState Identity a

lexer :: GenTokenParser String PState Identity
lexer = lexer' { whiteSpace = oneOf " \t" >> return ()}
    where
        lexer' :: TokenParser PState
        lexer' = makeTokenParser $ 
                    emptyDef { reservedNames = rNames
                             , identStart  = alphaNum <|> char '_'
                             , identLetter = alphaNum <|> char '_'
                             , caseSensitive = True
                             }

-- | Nombres reservados de las declaraciones. 
rNames :: [String]
rNames = [ "let", "fun", "spec"
         , "thm", "prop", "val"
         , ":", "=", ".", "with"
         , "end", "import", "module"
         ]

keyword :: String -> ParserD ()
keyword  = reserved lexer

keywordModule :: ParserD ()
keywordModule = keyword "module"

keywordImport :: ParserD ()
keywordImport = keyword "import"

keywordLet :: ParserD ()
keywordLet = keyword "let"

keywordDot :: ParserD ()
keywordDot = keyword "."

keywordWith :: ParserD ()
keywordWith = keyword "with"

keywordEnd :: ParserD ()
keywordEnd = keyword "end"

whites :: ParserD ()
whites = whiteSpace lexer

tryNewline :: ParserD ()
tryNewline = try newline >> return ()

manyTillWithEnd :: (Stream s m t) => ParsecT s u m a -> ParsecT s u m end -> 
                   ParsecT s u m ([a],end)
manyTillWithEnd p end = scan
    where
        scan =  do{e <- end; return ([],e) }
            <|> do{ x <- p; xs <- scan; return (x:fst xs,snd xs)}
