-- | Este modulo es el parser de modulos de fun.
module Fun.Parser.Module where

-- Imports de parsec.
import Text.Parsec

import Control.Lens

-- Imports fun.
import Fun.Parser.Internal
import Fun.Parser.Import
import Fun.Parser.Decl
import Fun.Module

-- | Parser de modulos de fun.
parseModule :: ParserD Module
parseModule = do
        _ <- keywordModule
        mName <- parseModuleName
        imps <- manyTill parseImport (parseDecls mName)
        _ <- manyTill (parseDecls mName <|> parseComments) eof
        st <- getState
        return $ Module mName imps (st ^. pdcls) emptyInDeclsVerifs [] []

parseComments :: ParserD ()
parseComments = many1 (lineComment 
                     <|> blockComment 
                     <|> tryNewline
                     ) >> return ()

parseFromStringModule :: String -> Either ParseError Module
parseFromStringModule = runParser parseModule initPState ""
