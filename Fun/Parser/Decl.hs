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
                                    , pProofSet, lastProofName
                                    , EitherName
                                    , ParenFlag(UseParen,UnusedParen)
                                    , PExprStateClass
                                    , PProofStateClass
                                    , pExprState, setExprState
                                    , pProofState
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
                       , Proof)
import Equ.Rule (Relation)
import Equ.Theories(createTheorem)

-- Imports de Parsec.
import Text.Parsec
import Text.Parsec.Error(setErrorPos)
import Text.Parsec.Token(lexeme)

-- Imports Data.*
import Data.Text(Text,pack)
import Data.Maybe (fromMaybe,fromJust)
import qualified Data.Map as M (empty,Map,member,insert,(!),lookup) 

-- Imports Monad.
import Control.Monad.Identity (unless, Identity)
import Control.Applicative ((<$>),(<*>))

-- Imports Fun.
import Fun.Decl
import Fun.Decl.Error (DeclPos (..))
import Fun.Declarations( Declarations
                      , vals, functions, props, specs
                      , envAddFun, envAddVal, envAddProp
                      , envAddSpec, envAddTheorem
                      , initDeclarations)
import Fun.Parser.Internal

-- Tipos para unificar la función de parseo para funciones y especificaciones.
type S = (Variable -> [Variable] -> PE.PreExpr -> SpecDecl)
type F = (Variable -> [Variable] -> PE.PreExpr -> Maybe Text -> FunDecl)
type UnifySF = Either S F


-- | Uso del parser de una expresión definido en 'Equ.Parser.Expr'.
-- TODO Ale: No esta bonito como manejamos el pasaje de errores con pass
-- ademas pasa que tenemos que re-acomodar la posición del error.
-- (Actualización) Tengo bastante avanzado en como solucionar esto y agregar
-- ademas mucha mas informacion sobre los errores de parseo.
-- parseExpr :: Maybe [Variable] -> ParserD () -> ParserD PE.PreExpr
-- parseExpr mvs till = getState >>= \st ->
--                      fmap (exprL $ pExprs st) (manyTill anyChar till) >>= pass
--     where
--         pass :: Either ParseError PE.Focus -> ParserD PE.PreExpr
--         pass ef = case ef of
--                     Right f -> return (PE.toExpr f)
--                     Left per -> getPosition >>= \p -> 
--                                 fail $ show $ flip setErrorPos per $
--                                 setSourceLine (errorPos per) (sourceLine p-1)
--         exprL' :: EquP.Parser' PE.Focus
--         exprL' = fmap (PE.toFocus . PE.unParen) (spaces >> EquP.parsePreExpr)
--         exprL :: EquP.PExprState -> String -> Either ParseError PE.Focus
--         exprL vt = runParser exprL' vt ""

parseExpr ::  ParserD PE.PreExpr
parseExpr = EquP.parsePreExpr

-- | Parsea el tipo de una función.
parseFunType :: ParserD Type
parseFunType = parseType'

-- | Parsea el tipo de una variable.
parseVarType :: ParserD Type
parseVarType = parseType'

-- | Parser general de tipos.
parseType' :: ParserD Type
parseType' = fmap EquP.parseTyFromString (manyTill anyChar (try (char '\n'))) 
             >>= pass
    where
        pass :: Either ParseError Type -> ParserD Type
        pass ef = case ef of
                    Right e -> return e
                    Left per -> getPosition >>= \p -> 
                                fail $ show $ flip setErrorPos per $
                                setSourceLine (errorPos per) (sourceLine p-1)

-- | Parsea prefijos de declaraciones y continua con p.
parseLet :: String -> ParserD () -> ParserD ()
parseLet s parse = try $ do many newline
                            keywordLet
                            keyword s
                            parse
                            many newline
                            return ()

-- | Parsea prefijos para declaración de pruebas.            
parseBeginProof :: ParserD () -> ParserD ()
parseBeginProof parse = try $ do 
                        many newline
                        keywordBegin
                        keywordProof
                        parse
                        many newline
                        return ()

-- | Parsea nombres que comienzan con minuscula.
parseName :: ParserD Text
parseName = lower >>= \lc -> fmap (pack . (lc :)) (many1 letter)

parseVar :: ParsecT String u Identity Variable
parseVar = EquP.parseVariable

parseFuncPreExpr :: ParsecT String u Identity Variable
parseFuncPreExpr = EquP.parseVariable

-- | Parser general para funciones y especificaciones.
{- | Comprobaciones al parsear:
    1. Una func/spec no puede haber sido declarada antes con el mismo nombre.
    2. Las variables y funciones que esten en la expresión relacionada con la 
        func/spec deben estar declaradas antes, o para el caso de las variables
        que este entre las variables de los argumentos.
-}
parseSF :: UnifySF -> Text -> ParserD ()
parseSF ecnstr modName = getParserState >>= \state -> parseFuncPreExpr >>= \fun -> 
                 (\pst ->   parseFunWithType fun pst
                        <|> parseFunWithoutType fun pst) (statePos state)
    where
        parseFunWithoutType :: Variable -> SourcePos -> ParserD ()
        parseFunWithoutType fun beginPos = do
            vs <- parseFunArgs
            many (whites <|> tryNewline)
            case ecnstr of
                Left cnstr -> parseS fun cnstr vs beginPos
                Right cnstr -> parseF fun cnstr vs beginPos
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
            e <- parseExpr -- (Just vs) tryNewline
            many (whites <|> tryNewline) 
            mname <- (parseTheoName <|> (keywordEnd >> return Nothing))
            state <- getParserState
            let declPos = DeclPos { begin = beginPos 
                                  , end = statePos state
                                  , moduleName = modName
                                }
            modifyState (\st -> 
                    st {pDecls = envAddFun (pDecls st) (declPos,cnstr fun vs e mname)}) 
        parseTheoName :: ParserD (Maybe Text)
        parseTheoName = Just <$> (keywordDeriving >> keywordFrom >> parseName)
        parseS :: Variable -> S -> [Variable] -> SourcePos -> ParserD ()
        parseS fun cnstr vs beginPos = do
            e <- parseExpr --(Just vs) keywordEnd
            keywordEnd
            state <- getParserState
            let declPos = DeclPos { begin = beginPos 
                                  , end = statePos state
                                  , moduleName = modName
                            }
            modifyState (\st -> 
                    st {pDecls = envAddSpec (pDecls st) (declPos,cnstr fun vs e)})
        parseFunArgs :: ParserD [Variable]
        parseFunArgs = manyTill parseVar (try $ string "=")

-- | Parsea una especificación.
parseSpec :: Text -> ParserD ()
parseSpec modName = parseSF (Left Spec) modName

-- | Parsea una función.
parseFun :: Text -> ParserD ()
parseFun modName = parseSF (Right Fun) modName

-- | Parser de relaciones en ParserD, parsea hasta un terminador till.
parseRel :: ParserD () -> ParserD Relation
parseRel till = do
                st <- getState
                fmap (parseRel' (pProofs st)) (manyTill anyChar till) >>= pass
    where
        pass :: Either ParseError Relation -> ParserD Relation
        pass er = case er of
                    Right r -> return r
                    Left per -> getPosition >>= \p -> 
                                fail $ show $ flip setErrorPos per $
                                setSourceLine (errorPos per) (sourceLine p-1)
        parseRel' :: EquP.PProofState -> String -> Either ParseError Relation
        parseRel' pps = runParser EquP.rel pps ""

-- | Parser de pruebas para parserD, parsea una prueba hasta el terminador till.
-- parseProof :: ParserD () -> ParserD Proof
-- parseProof till = do 
--                 st <- getState
--                 fmap (parseProof' (pProofs st)) (manyTill anyChar till) >>= pass
--     where
--         pass :: Either ParseError Proof -> ParserD Proof
--         pass ep = case ep of
--                     Right p -> return p
--                     Left per -> getPosition >>= \p ->
--                                 fail (show $ flip setErrorPos per $
--                                 setSourceLine (errorPos per) (sourceLine p-1))
--         parseHack :: String -> String
--         parseHack s = "begin proof " ++ s ++ "end proof"
--         parseProof' :: EquP.PProofState -> String -> Either ParseError Proof
--         parseProof' pps s = runParser (EquP.proof Nothing True) pps "" (parseHack s)
parseProof :: ParserD Proof
parseProof = EquP.proof Nothing False

-- | Parsea un teorema.
-- TODO: Mejorar el informe de errores.
parseThm :: Text -> ParserD ()
parseThm modName = do
    state <- getParserState
    let beginPos = statePos state
--     name <- parseName
--     many (whites <|> tryNewline)
--     p <- parseProof -- (try $ keywordEnd >> keywordProof)
--     keywordEnd
--     keywordProof
    p <- parseProof
    state <- getState
    let mname = EquP.lastProofName $ pProofs state
    maybe (fail "Prueba sin nombre") (\name -> continue name p beginPos) mname
    
    
    where continue name p beginPos = do
            state <- getParserState
            let endPos = statePos state
            let declPos = DeclPos beginPos endPos modName
            let declThm = Thm $ createTheorem name p
            modifyState (\st -> st { pDecls = envAddTheorem (pDecls st) (declPos,declThm)
                                , pProofs = addTheorem (pProofs st) name p
                                })

-- | Agrega un teorema parseado al estado de parseo de teoremas.
addTheorem :: EquP.PProofState -> Text -> Proof -> EquP.PProofState
addTheorem pst pn p = 
        let proofSet = EquP.pProofSet pst in
            case M.lookup pn proofSet of
                (Just (Just _)) -> pst
                _ -> let proofSetUpdated = M.insert pn (Just p) proofSet in
                            pst {EquP.pProofSet = proofSetUpdated}

-- | Parser para declaracion de valores.
{- | Comprobaciones al parsear:
    1. Un val no puede haber sido declarado antes con el mismo nombre.
    2. Las variables y funciones que esten en la expresión relacionada con la 
        func/spec deben estar declaradas antes.
-}
parseVal :: Text -> ParserD ()
parseVal modName = parseVar >>= \v -> getParserState >>= \state ->
           (\pst -> parseVarWithoutType v pst modName
                <|> parseVarWithType v pst modName) (statePos state) 
    where 
        parseVarWithoutType :: Variable -> SourcePos -> Text -> ParserD ()
        parseVarWithoutType v beginPos modName = try $
                keyword "=" >> parseExpr -- Nothing tryNewline 
                >>= \e ->
                many (whites <|> tryNewline) >> 
                getParserState >>= \state ->
                (\declPos -> modifyState (\st -> 
                    st {pDecls = envAddVal (pDecls st) (declPos,Val v e)})
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
parseProp :: Text -> ParserD ()
parseProp modName = do
        state <- getParserState
        let beginPos = statePos state
        name <- parseName
        e <- parseExpr -- Nothing keywordEnd
        keywordEnd
        state <- getParserState
        let endPos = statePos state
        let declPos = DeclPos beginPos endPos modName
        modifyState (\st -> st {pDecls = envAddProp (pDecls st) (declPos,Prop name e)})

-- | Parser de declaraciones.
parseDecl :: Text -> ParserD ()
parseDecl modName = 
             parseLet "spec" (parseSpec modName)
         <|> parseLet "prop" (parseProp modName)
         <|> --parseBeginProof (parseThm modName)
             (parseThm modName)
         <|> parseLet "fun"  (parseFun modName)
         <|> parseLet "val"  (parseVal modName)

-- | Parsea una declaración en desde un string.
parseFromStringDecl :: String -> Either ParseError ()
parseFromStringDecl = runParser (parseDecl $ pack "") initPState ""

-- | Estado inicial del parser.
initPState :: PDeclState
initPState = PDeclState { pDecls = initDeclarations
                        , pExprs = EquP.initPExprState EquP.UnusedParen
                        , pProofs = EquP.initPProofState $ EquP.initPExprState EquP.UnusedParen
                        }
