-- | Este modulo es el parser de declaraciones.
module Fun.Parser.Decl where

-- Imports de EQU.
import Equ.Syntax (var, tRepr,Variable(..),VarName,FuncName,Func(..),tType)
import qualified Equ.Parser as EquP ( parsePreExpr
                                    , parseTyFromString
                                    , parseVariable
                                    , parseVariableWithType
                                    , rel, proof
                                    , initPProofState
                                    , initPExprState
                                    , PProofState 
                                    , PExprState
                                    , pTheoSet
                                    , EitherName
                                    , ParenFlag(UseParen,UnusedParen)
                                    , PExprStateClass (..)
                                    , PProofStateClass (..)
                                    , parseType
                                    )
import qualified Equ.PreExpr as PE ( PreExpr, PreExpr' (Var)
                                   , toFocus,Focus,unParen
                                   , listOfVar
                                   , toExpr
                                   )
import Equ.Types(Type, tyVarInternal)
import Equ.Proof.Proof ( getEnd 
                       , getRel
                       , getStart
                       , Proof
                       , thExpr)
import Equ.Expr
import Equ.Rule (Relation)
import Equ.Theories(createTheorem)

-- Imports de Parsec.
import Text.Parsec
import Text.Parsec.Error(setErrorPos)
import Text.Parsec.Token(lexeme)

-- Imports Data.*
import Data.Text(Text,pack,unpack)
import Data.Maybe (fromMaybe,fromJust)
import qualified Data.Map as M (empty,Map,member,insert,(!),lookup) 

-- Imports Monad.
-- import Control.Monad.Identity (unless, Identity)
import Data.Functor.Identity
import Control.Applicative ((<$>),(<*>))

-- Imports Fun.
import Fun.Decl
import Fun.Decl.Error (DeclPos (..))
import Fun.Declarations( Declarations
                      , vals, functions, props, specs
                      , envAddFun, envAddVal, envAddProp
                      , envAddSpec, envAddTheorem, envAddDeriv
                      , initDeclarations)
import Fun.Parser.Internal
import Fun.Module

-- Tipos para unificar la función de parseo para funciones y especificaciones.
type S = (Variable -> [Variable] -> PE.PreExpr -> SpecDecl)
type F = (Variable -> [Variable] -> PE.PreExpr -> Maybe Text -> FunDecl)
type UnifySF = Either S F

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
parseLet s parse = try $ do many newline
                            keywordLet
                            keyword s
                            parse
                            many newline
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
parseSF :: UnifySF -> Text -> ParserD ()
parseSF ecnstr modName = getParserState >>= \state -> 
                         try parseFuncPreExpr >>= \fun -> 
                         let pst = statePos state in
                         parseFunWithType fun pst <|> 
                         parseFunWithoutType fun pst
    where
        parseFunWithoutType :: Variable -> SourcePos -> ParserD ()
        parseFunWithoutType fun beginPos = do
            vs <- parseFunArgs
            many (whites <|> tryNewline)
            let vs' = if head vs == fun then tail vs else vs
            case ecnstr of
                Left cnstr  -> parseS fun cnstr vs' beginPos
                Right cnstr -> parseF fun cnstr vs' beginPos
        parseFunWithType :: Variable -> SourcePos -> ParserD ()
        parseFunWithType fun beginPos = try $
                keyword ":" >>
                parseFunType >>= \ty -> 
                many (whites <|> tryNewline) >>
                parseFuncPreExpr >>= \fun' ->
                if fun /= fun' 
                then fail (show fun ++ " != " ++ show fun') 
                else parseFunWithoutType (var (tRepr fun) ty) beginPos
        parseF :: Variable -> F -> [Variable] -> SourcePos -> ParserD ()
        parseF fun cnstr vs beginPos = do
            e <- parseExpr
            many (whites <|> tryNewline) 
            mname <- (parseTheoName <|> (keywordEnd >> return Nothing))
            state <- getParserState
            let declPos = DeclPos { begin = beginPos 
                                  , end = statePos state
                                  , moduleName = modName
                                }
            modifyState (\st -> 
                    st {pDecls = envAddFun  (declPos,cnstr fun vs e mname) (pDecls st)}) 
        parseTheoName :: ParserD (Maybe Text)
        parseTheoName = Just <$> (keywordVerified >> keywordFrom >> parseName)
        parseS :: Variable -> S -> [Variable] -> SourcePos -> ParserD ()
        parseS fun cnstr vs beginPos = do
            e <- parseExpr
            keywordEnd
            state <- getParserState
            let declPos = DeclPos { begin = beginPos 
                                  , end = statePos state
                                  , moduleName = modName
                            }
            modifyState (\st -> 
                    st {pDecls = envAddSpec  (declPos,cnstr fun vs e) (pDecls st)})
        parseFunArgs :: ParserD [Variable]
        parseFunArgs = manyTill parseVar (try $ string defSymbol)

-- | Parsea una especificación.
parseSpec :: ModName -> ParserD ()
parseSpec = parseSF (Left Spec) 

-- | Parsea una función.
parseFun :: ModName -> ParserD ()
parseFun = parseSF (Right Fun)

-- | Parser de relaciones en ParserD, parsea hasta un terminador till.
-- parseRel :: ParserD () -> ParserD Relation
-- parseRel till = do
--                 st <- getState
--                 fmap (parseRel' (pProofs st)) (manyTill anyChar till) >>= pass
--     where
--         pass :: Either ParseError Relation -> ParserD Relation
--         pass er = case er of
--                     Right r -> return r
--                     Left per -> getPosition >>= \p -> 
--                                 fail $ show $ flip setErrorPos per $
--                                 setSourceLine (errorPos per) (sourceLine p-1)
--         parseRel' :: EquP.PProofState -> String -> Either ParseError Relation
--         parseRel' pps = runParser EquP.rel pps ""

parseProof :: ParserD Proof
parseProof = EquP.proof Nothing True

-- | Parsea un teorema.
-- TODO: Mejorar el informe de errores.
parseThm :: Text -> ParserD ()
parseThm modName = do
    state <- getParserState
    let beginPos = statePos state
    name <- parseName
    many (whites <|> tryNewline)
    keywordDefSymbol
    e <- parseExpr
    p <- parseProof
    state <- getParserState
    let endPos = statePos state
    let declPos = DeclPos beginPos endPos modName
    let t = createTheorem name p
    let declThm = Thm $ t
    let proofExpr = thExpr t
    -- Este chequeo deberia ir en el chequeo de módulos y no acá.
    if proofExpr /= Expr e
       then fail "La expresión de la declaración del teorema no coincide con la prueba"
       else modifyState (\st -> st { pDecls = envAddTheorem  (declPos,declThm) (pDecls st) })

-- | Agrega un teorema parseado al estado de parseo de teoremas.
addTheorem :: EquP.PProofState -> Text -> Proof -> EquP.PProofState
addTheorem pst pn p = 
        let theoSet = EquP.pTheoSet pst in
            case M.lookup pn theoSet of
                (Just _) -> pst
                _ -> let theo = createTheorem pn p
                         proofSetUpdated = M.insert pn theo theoSet 
                     in pst {EquP.pTheoSet = proofSetUpdated}

-- | Parser para declaracion de valores.
{- | Comprobaciones al parsear:
    1. Un val no puede haber sido declarado antes con el mismo nombre.
    2. Las variables y funciones que esten en la expresión relacionada con la 
        func/spec deben estar declaradas antes.
-}
parseVal :: ModName -> ParserD ()
parseVal modName = parseVar >>= \v -> getParserState >>= \state ->
           (\pst -> parseVarWithoutType v pst modName
                <|> parseVarWithType v pst modName) (statePos state) 
    where 
        parseVarWithoutType :: Variable -> SourcePos -> Text -> ParserD ()
        parseVarWithoutType v beginPos modName = try $
                keywordDefSymbol >> parseExpr
                >>= \e ->
                many (whites <|> tryNewline) >> 
                keywordEnd >>
                getParserState >>= \state ->
                (\declPos -> modifyState (\st -> 
                    st {pDecls = envAddVal  (declPos,Val v e) (pDecls st)})
                    ) (DeclPos beginPos (statePos state) modName)
        parseVarWithType :: Variable -> SourcePos -> Text -> ParserD ()
        parseVarWithType v beginPos modName = try $
                    keyword ":" >>
                    parseFunType >>= \ty ->
                    parseVar >>= \v' ->
                    if v /= v' 
                        then fail (show v ++ " != " ++ show v') 
                        else parseVarWithoutType (var (tRepr v) ty) beginPos modName

-- | Parser para propiedades.
parseProp :: ModName -> ParserD ()
parseProp modName = do
        state <- getParserState
        let beginPos = statePos state
        name <- parseName
        many (whites <|> tryNewline)
        keywordDefSymbol
        --many (whites <|> tryNewline)
        e <- parseExpr
        many (whites <|> tryNewline)
        keywordEnd
        state <- getParserState
        let endPos = statePos state
        let declPos = DeclPos beginPos endPos modName
        modifyState (\st -> st {pDecls = envAddProp 
                                            (declPos,Prop name e)
                                            (pDecls st) 
                                })

-- | Parser de derivaciones.
parseDer :: ModName -> ParserD ()
parseDer modName = do
        state <- getParserState
        let beginPos = statePos state
        name <- parseVar
        keywordBy
        keywordRecursion
        keywordOn
        var <- parseVar
        fps <- many1 parseCases
        keywordEnd
        let endPos = statePos state
        let declPos = DeclPos beginPos endPos modName
        modifyState (\st -> st {pDecls = envAddDeriv 
                                          (declPos,Deriv name var $ reverse fps)
                                          (pDecls st) 
                               })
    where
        parseCases :: ParserD (PE.Focus, Proof)
        parseCases = do
                    keywordCase
                    f <- PE.toFocus <$> parseExpr
                    keywordRArrow
                    p <- EquP.proof Nothing False
                    return (f,p)

-- | Parser de declaraciones.
parseDecl :: ModName -> ParserD ()
parseDecl modName = 
             parseLet "spec"       (parseSpec modName)
         <|> parseLet "prop"       (parseProp modName)
         <|> parseLet "fun"        (parseFun modName)
         <|> parseLet "val"        (parseVal modName)
         <|> parseLet "derivation" (parseDer modName)
         <|> parseLet "thm"        (parseThm modName)

-- | Parsea una declaración en desde un string.
parseFromStringDecl :: String -> Either ParseError ()
parseFromStringDecl = runParser (parseDecl $ pack "") initPState ""

-- | Estado inicial del parser.
initPState :: PDeclState
initPState = PDeclState { pDecls = initDeclarations
                        , pExprs = EquP.initPExprState EquP.UnusedParen
                        , pProofs = EquP.initPProofState M.empty $ EquP.initPExprState EquP.UnusedParen
                        }
