-- | Este modulo es el parser de modulos de fun.
module Fun.Parser.Module where

import System.Environment

-- Imports de parsec.
import Text.Parsec

-- Imports fun.
import Fun.Parser.Internal
import Fun.Parser.Import
import Fun.Parser.Decl
import Fun.Declarations
import Fun.Module

-- | Parser de modulos de fun.
parseModule :: ParserD Module
parseModule = do
        keywordModule
        mName <- parseModuleName
        imports <- manyTill parseImport (parseDecl mName)
        manyTill (parseDecl mName <|> parseComments) eof
        st <- getState
        return $ Module mName imports (pDecls st) emptyInDeclsVerifs [] []
    where
        emptyInDeclsVerifs :: InvalidDeclsAndVerifs
        emptyInDeclsVerifs = InvalidDeclsAndVerifs emptyInDeclarations []
        parseComments :: ParserD ()
        parseComments = many1 ( lineComment 
                             <|> blockComment 
                             <|> tryNewline
                              ) >> return ()

parseFromStringModule :: String -> Either ParseError Module
parseFromStringModule = runParser parseModule initPState ""
