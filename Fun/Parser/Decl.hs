-- | Este modulo es el parser de declaraciones.
module Fun.Parser.Decl where

-- Imports de EQU.
import Equ.Syntax (var, tRepr,Variable(..))
import qualified Equ.Parser as EquP ( parsePreExpr
                                    , parseVariable
                                    , proof
                                    , initPProofState
                                    , initPExprState
                                    , ParenFlag(UnusedParen)
                                    , parseType
                                    )
import qualified Equ.PreExpr as PE ( PreExpr
                                   , toFocus
                                   , Focus
                                   )
import Equ.Types (Type)
import Equ.Proof.Proof (Proof, thExpr)
import Equ.Expr
import Equ.Theories(createTheorem)

-- Imports de Parsec.
import Text.Parsec
import Text.Parsec.Token(lexeme)

-- Imports Data.*
import Data.Text(Text,pack)
import qualified Data.Map as M (empty) 

import Control.Lens
-- Imports Monad.
import Control.Applicative ((<$>),(<*>),(<$),(<*))

-- Imports Fun.
import Fun.Decl
import Fun.Declarations ( Annot
                        , Declarations
                        , props
                        , derivs
                        , functions
                        , vals
                        , specs
                        , theorems
                        , initDeclarations)
import Fun.Parser.Internal
import Fun.Module

-- | Parser de preExpresiones.
parseExpr ::  ParserD PE.PreExpr
parseExpr = EquP.parsePreExpr

-- | Parsea el tipo de una función.
parseFunType :: ParserD Type
parseFunType = EquP.parseType

-- | Parsea el tipo de una variable.
parseVarType :: ParserD Type
parseVarType = EquP.parseType

-- | Parsea prefijos de declaraciones y continua con @parse@.
parseLet :: String -> ParserD () -> ParserD ()
parseLet s p = try $  many newline >> 
                      keywordLet >>
                      keyword s >> 
                      p >>
                      many newline >> 
                      return ()

-- | Parsea nombres que comienzan con minuscula.
parseName :: ParserD Text
parseName = lexeme lexer ((:) <$> lower <*> many alphaNum) >>= return . pack

parseVar :: ParserD Variable
parseVar = EquP.parseVariable

parseFuncPreExpr :: ParserD Variable
parseFuncPreExpr = EquP.parseVariable


-- | Parser general para funciones y especificaciones.
{- | Comprobaciones al parsear:
    1. Una func/spec no puede haber sido declarada antes con el mismo nombre.
    2. Las variables y funciones que esten en la expresión relacionada con la 
        func/spec deben estar declaradas antes, o para el caso de las variables
        que este entre las variables de los argumentos.
-}

parseFun :: ModName -> ParserD ()
parseFun mName = parseDecl mName (parseWithType parseFunUndec) functions

parseFunUndec :: Variable -> ParserD FunDecl
parseFunUndec fun = Fun fun <$> parseFunArgs
                            <*  many (whites <|> tryNewline)
                            <*> parseExpr 
                            <*  many (whites <|> tryNewline)
                            <*> (parseTheoName <|> (keywordEnd >> return Nothing))

parseSpec :: ModName -> ParserD ()
parseSpec mName = parseDecl mName (parseWithType parseSpecUndec) specs

parseSpecUndec :: Variable -> ParserD SpecDecl
parseSpecUndec fun = Spec fun <$> parseFunArgs
                              <*  many (whites <|> tryNewline)
                              <*> parseExpr 
                              <*  keywordEnd

parseFunArgs :: ParserD [Variable]
parseFunArgs = manyTill parseVar (try $ string defSymbol)

parseTheoName :: ParserD (Maybe Text)
parseTheoName = Just <$> (keywordVerified >> keywordFrom >> parseName)

parseProof :: ParserD Proof
parseProof = EquP.proof Nothing True

-- | Parsea un teorema.
-- TODO: Mejorar el informe de errores.
parseThm :: Text -> ParserD ()
parseThm mName = parseDecl mName parseTheo theorems
    where parseTheo = do name <- parseName
                         _ <- many (whites <|> tryNewline)
                         _ <- keywordDefSymbol
                         e <- parseExpr
                         p <- parseProof
                         let t = createTheorem name p
                         let declThm = Thm $ t
                         let proofExpr = thExpr t
                         -- Este chequeo deberia ir en el chequeo de módulos y no acá.
                         if proofExpr /= Expr e
                            then fail "La expresión de la declaración del teorema no coincide con la prueba"
                            else return declThm


-- | Parser para declaracion de valores.
{- | Comprobaciones al parsear:
    1. Un val no puede haber sido declarado antes con el mismo nombre.
    2. Las variables y funciones que esten en la expresión relacionada con la 
        func/spec deben estar declaradas antes.
-}
parseVal :: ModName -> ParserD ()
parseVal mName = parseDecl mName (parseWithType parseValueUndec) vals

parseValueUndec :: Variable -> ParserD ValDecl
parseValueUndec v = Val v <$  keywordDefSymbol
                          <*> parseExpr
                          <*  many (whites <|> tryNewline)
                          <*  keywordEnd 

-- | Parser para propiedades.
parseProp :: ModName -> ParserD ()
parseProp mName = parseDecl mName parsePrp props
          where parsePrp = Prop <$> parseName
                                <*  many (whites <|> tryNewline)
                                <*  keywordDefSymbol
                                <*> parseExpr
                                <*  many (whites <|> tryNewline)
                                <*  keywordEnd

-- | Parser de derivaciones.
parseDer :: ModName -> ParserD ()
parseDer mName = parseDecl mName parseDeriv derivs
         where parseDeriv = Deriv <$> parseVar
                                  <*  keywordBy
                                  <*  keywordRecursion
                                  <*  keywordOn
                                  <*> parseVar
                                  <*> (reverse <$> many1 parseCases)
                                  <*  keywordEnd

               parseCases :: ParserD (PE.Focus, Proof)
               parseCases = do
                    _ <- keywordCase
                    f <- PE.toFocus <$> parseExpr
                    _ <- keywordRArrow
                    p <- EquP.proof Nothing False
                    return (f,p)

parseWithType :: Decl a => (Variable -> ParserD a) -> ParserD a
parseWithType p = parseVar >>= \v ->
                  (p v <|> parseTyped v p)
    where parseTyped v p' = try $ keyword ":" >> parseFunType >>= \ty ->
                                 parseVar >>= \v' ->
                                 if v /= v' 
                                 then fail (show v ++ " != " ++ show v') 
                                 else p' (var (tRepr v) ty)


parseDecl :: ModName-> ParserD a -> Setting' (->) Declarations [Annot a] -> ParserD ()
parseDecl m p upd = parseWithPos m p >>= \d -> modifyState (pdcls . upd %~ (d:))
                    

-- | Parser de declaraciones.
parseDecls :: ModName -> ParserD ()
parseDecls mName = 
             parseLet "spec"       (parseSpec mName)
         <|> parseLet "prop"       (parseProp mName)
         <|> parseLet "fun"        (parseFun mName)
         <|> parseLet "val"        (parseVal mName)
         <|> parseLet "derivation" (parseDer mName)
         <|> parseLet "thm"        (parseThm mName)

-- | Parsea una declaración en desde un string.
parseFromStringDecl :: String -> Either ParseError ()
parseFromStringDecl = runParser (parseDecls $ pack "") initPState ""

-- | Estado inicial del parser.
initPState :: PDeclState
initPState = PDeclState { pDecls = initDeclarations
                        , pExprs = EquP.initPExprState EquP.UnusedParen
                        , pProofs = EquP.initPProofState M.empty $ EquP.initPExprState EquP.UnusedParen
                        }
