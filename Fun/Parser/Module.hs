----------------------------------------------------------------------------
-- |
-- Module      :  $Header$
-- Copyright   :  (c) Proyecto Theona, 2012-2013
--                (c) Alejandro Gadea, Emmanuel Gunther, Miguel Pagano
-- License     :  <license>
-- 
-- Maintainer  :  miguel.pagano+theona@gmail.com
-- Stability   :  experimental
-- Portability :  portable
--
-- Parser de modulos de fun.
-- 
----------------------------------------------------------------------------
module Fun.Parser.Module where

-- Imports de parsec.
import Text.Parsec
import Text.Parsec.Token(lexeme)
import Data.Text (pack)

import Control.Lens
import Control.Monad ( void )
import Control.Applicative ((<$>),(<*>))

-- Imports fun.
import Fun.Parser.Internal
import Fun.Parser.Pragma
import Fun.Parser.Decl
import Fun.Module

-- | Parser de modulos de fun.
parseModule :: ParserD Module
parseModule = do
        void $ choice [ try $ skipMany1 $ choice [ whites, void $ newline]
                      , return ()
                      ]
        pragma <- choice [try parsePragma, return []]
        void $ keywordModule
        mName <- parseModuleName
        imps <- manyTill parseImport (parseDecls mName)
        void $ manyTill (parseDecls mName <|> parseComments) eof
        st <- getState
        return $ Module pragma mName imps (st ^. pdcls) emptyInDeclsVerifs [] []

parseComments :: ParserD ()
parseComments = many1 (lineComment
                     <|> blockComment
                     <|> tryNewline
                     ) >> return ()

-- | Parsea un nombre de modulo.
parseModuleName :: ParserD ModName
parseModuleName = fmap pack (lexeme lexer ((:) <$> upper <*> many alphaNum))

-- | Parser de import.
parseImport :: ParserD Import
parseImport = fmap Import (keywordImport >> parseModuleName)


parseFromStringModule :: String -> Either ParseError Module
parseFromStringModule = runParser parseModule initPState ""
