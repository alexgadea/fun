-- | Este modulo es el parser de imports.
module Fun.Parser.Import where

-- Imports Monad and Applicative.
import Control.Applicative ((<$>),(<*>))

-- Imports parsec.
import Text.Parsec
import Text.Parsec.Token(lexeme)

-- Imports Data.*
import Data.Text(pack)

-- Imports de fun.
import Fun.Parser.Internal
import Fun.Module

-- | Parsea un nombre de modulo.
parseModuleName :: ParserD ModName
parseModuleName = fmap pack (lexeme lexer ((:) <$> upper <*> many alphaNum))

-- | Parser de import.
parseImport :: ParserD Import
parseImport = fmap Import (keywordImport >> parseModuleName)
