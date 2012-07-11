-- | Este modulo es el parser de modulos de fun.
module Fun.Parser.Module where

import System.Environment

-- Imports de parsec.
import Text.Parsec

-- Imports fun.
import Fun.Parser.Internal
import Fun.Parser.Import
import Fun.Parser.Decl
import Fun.Derivation
import Fun.Module

-- | Parser de modulos de fun.
parseModule :: ParserD Module
parseModule = do
            keywordModule
            mName <- parseModuleName
            imports <- manyTill parseImport parseDecl
            manyTill parseDecl eof
            st <- getState
            return $ Module mName imports (pDecls st) []

parseFromStringModule :: String -> Either ParseError Module
parseFromStringModule = runParser parseModule initPState ""
