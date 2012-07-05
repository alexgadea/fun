-- | Este modulo es el parser de declaraciones.
module Fun.Parser.Decl where

-- Imports de EQU.
import Equ.Syntax(var, tRepr,Variable,VarName,FuncName,Func(..))
import qualified Equ.Parser as EquP ( Parser'
                                    , parsePreExpr,parseTyFromString
                                    , rel, proof
                                    , initPProofState
                                    , initPExprState
                                    , PProofState 
                                    , PExprState
                                    )
import qualified Equ.PreExpr as PE ( PreExpr, PreExpr' (Var), PreExpr' (Fun)
                                   , toFocus,Focus,unParen
                                   , listOfVar,listOfFun
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
import qualified Data.Map as M (empty,Map,member,insert,(!)) 

-- Imports Monad.
import Control.Monad.Identity (unless, Identity)
import Control.Applicative ((<$>),(<*>))

-- Imports Fun.
import Fun.Decl
import Fun.Declarations( Declarations
                      , vals, functions, props, specs
                      , envAddFun, envAddVal, envAddProp
                      , envAddSpec, envAddTheorem
                      , initDeclarations)
import Fun.Parser.Internal

-- Tipos para unificar la función de parseo para funciones y especificaciones.
type S = (Func -> [Variable] -> PE.PreExpr -> SpecDecl)
type F = (Func -> [Variable] -> PE.PreExpr -> Maybe Text -> FunDecl)
type UnifySF = Either S F

-- | Calcula el tipo de una variable o funcion
setType :: Either VarName FuncName -> PDeclState -> (PDeclState,Type)
setType name st = 
        if name `M.member` maps
            then (st, maps M.! name)
            else (st {pVarTy = (n+1, M.insert name newvar maps)},newvar)
    where 
        maps :: M.Map (Either VarName FuncName) Type
        maps = snd $ pVarTy st
        n :: Int
        n = fst $ pVarTy st
        newvar = tyVarInternal n

-- | Actualiza el tipo de una variable.
updateTypeVar :: EitherName -> Type -> ParserD ()
updateTypeVar = updateTypeVF

-- | Actualiza el tipo de una función.
updateTypeFun :: EitherName -> Type -> ParserD ()
updateTypeFun = updateTypeVF

-- | Función general para actualizar tipos.
updateTypeVF :: EitherName -> Type -> ParserD ()
updateTypeVF ename ty = getState >>= \st -> 
                       putState (st {pVarTy = (n st, ins st ename ty)})
    where
        n :: PDeclState -> Int
        n = fst . pVarTy
        maps :: PDeclState-> M.Map EitherName Type
        maps = snd . pVarTy
        ins :: PDeclState -> EitherName -> Type -> M.Map EitherName Type
        ins st ename ty = M.insert ename ty (maps st)

-- | Uso del parser de una expresión definido en 'Equ.Parser.Expr'.
-- TODO Ale: No esta bonito como manejamos el pasaje de errores con pass
-- ademas pasa que tenemos que re-acomodar la posición del error.
-- (Actualización) Tengo bastante avanzado en como solucionar esto y agregar
-- ademas mucha mas informacion sobre los errores de parseo.
parseExpr :: Maybe [Variable] -> ParserD () -> ParserD PE.PreExpr
parseExpr mvs till = getState >>= \st ->
                     fmap (exprL $ pVarTy st) (manyTill anyChar till) >>= pass
    where
        pass :: Either ParseError PE.Focus -> ParserD PE.PreExpr
        pass ef = case ef of
                    Right f -> return (PE.toExpr f)
                    Left per -> getPosition >>= \p -> 
                                fail $ show $ flip setErrorPos per $
                                setSourceLine (errorPos per) (sourceLine p-1)
        exprL' :: EquP.Parser' PE.Focus
        exprL' = fmap (PE.toFocus . PE.unParen) (spaces >> EquP.parsePreExpr)
        exprL :: EquP.PExprState -> String -> Either ParseError PE.Focus
        exprL vt = runParser exprL' vt ""

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

-- | Parser de variable. 
parseVar :: ParserD Variable
parseVar = try $ lexeme lexer ((:) <$> lower <*> many alphaNum) >>= 
           \v -> getState >>= 
           \st -> ((\ (st', t) -> putState st' >> return (var (pack v) t))
                  (setType (Left $ pack v) st))

-- | Parser de función.
parseFuncPreExpr :: ParserD Func
parseFuncPreExpr = try $ lexeme lexer ((:) <$> upper <*> many alphaNum) >>= 
                   \name -> fmap (setType (Right $ pack name)) getState >>=
                   \(st',t) -> putState st' >> return (makeFun name t)
    where
        makeFun :: String -> Type -> Func
        makeFun = Func . pack

-- | Parser general para funciones y especificaciones.
{- | Comprobaciones al parsear:
    1. Una func/spec no puede haber sido declarada antes con el mismo nombre.
    2. Las variables y funciones que esten en la expresión relacionada con la 
        func/spec deben estar declaradas antes, o para el caso de las variables
        que este entre las variables de los argumentos.
-}
parseSF :: UnifySF -> ParserD ()
parseSF ecnstr = parseFuncPreExpr >>= \fun -> 
            parseFunWithType fun <|> parseFunWithoutType fun
    where
        parseFunWithoutType :: Func -> ParserD ()
        parseFunWithoutType fun = do
            vs <- parseFunArgs
            case (ecnstr) of
                Left cnstr -> parseS fun cnstr vs
                Right cnstr -> parseF fun cnstr vs
        parseFunWithType :: Func -> ParserD ()
        parseFunWithType fun = try $
                keyword ":" >>
                parseFunType >>= \ty -> 
                updateTypeFun (Right $ tRepr fun) ty >>
                parseFuncPreExpr >>= \fun' ->
                if fun /= fun' 
                    then fail (show fun ++ " != " ++ show fun') 
                    else parseFunWithoutType fun'
        parseF :: Func -> F -> [Variable] -> ParserD ()
        parseF fun cnstr vs = do
            e <- parseExpr (Just vs) tryNewline
            st <- getState
            case isPrg e of
                False -> fail "La expresión no es un programa."
                _ -> do
                    mname <- (parseTheoName <|> return Nothing)
                    putState (st {pDecls = envAddFun (pDecls st) 
                                                     (cnstr fun vs e mname)}) 
        parseTheoName :: ParserD (Maybe Text)
        parseTheoName = keywordDerivingFrom >> parseName >>= return . Just
        parseS :: Func -> S -> [Variable] -> ParserD ()
        parseS fun cnstr vs = do
            e <- parseExpr (Just vs) tryNewline
            st <- getState
            putState (st {pDecls = envAddSpec (pDecls st) (cnstr fun vs e)})
        parseFunArgs :: ParserD [Variable]
        parseFunArgs = manyTill parseVar (try $ string "=")

-- | Parsea una especificación.
parseSpec :: ParserD ()
parseSpec = parseSF (Left Spec)

-- | Parsea una función.
parseFun :: ParserD ()
parseFun = parseSF (Right Fun)

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
        parseRel' pps s = runParser EquP.rel pps "" s

-- | Parser de pruebas para parserD, parsea una prueba hasta el terminador till.
parseProof :: ParserD () -> ParserD Proof
parseProof till = do 
                st <- getState
                fmap (parseProof' (pProofs st)) 
                     (manyTill anyChar till) >>= pass
    where
        pass :: Either ParseError Proof -> ParserD Proof
        pass ep = case ep of
                    Right p -> return p
                    Left per -> getPosition >>= \p -> 
                                fail $ show $ flip setErrorPos per $
                                setSourceLine (errorPos per) (sourceLine p-1)
        parseHack :: String -> String
        parseHack s = "begin proof" ++ s ++ "\nend proof"
        parseProof' :: EquP.PProofState -> String -> Either ParseError Proof
        parseProof' pps s = runParser (EquP.proof Nothing True) pps "" (parseHack s)

-- | Parsea un teorema.
-- TODO: Mejorar el informe de errores.
parseThm :: ParserD ()
parseThm = do
    name <- parseName
    p <- parseProof (try $ keywordEnd >> keywordProof)
    st <- getState
    let declThm = Thm $ createTheorem name p
    putState (st {pDecls = envAddTheorem (pDecls st) declThm})

-- | Parser para declaracion de valores.
{- | Comprobaciones al parsear:
    1. Un val no puede haber sido declarado antes con el mismo nombre.
    2. Las variables y funciones que esten en la expresión relacionada con la 
        func/spec deben estar declaradas antes.
-}
parseVal :: ParserD ()
parseVal = parseVar >>= \v -> parseVarWithoutType v <|> parseVarWithType v
    where 
        parseVarWithoutType :: Variable -> ParserD ()
        parseVarWithoutType v = try $
                keyword "=" >> parseExpr Nothing tryNewline >>= \e ->
                getState >>= \st -> 
                putState (st {pDecls = envAddVal (pDecls st) (Val v e)})
        parseVarWithType :: Variable -> ParserD ()
        parseVarWithType v = try $
                    keyword ":" >>
                    parseFunType >>= \ty -> 
                    updateTypeVar (Left $ tRepr v) ty >>
                    parseVar >>= \v' ->
                    if v /= v' 
                        then fail (show v ++ " != " ++ show v') 
                        else parseVarWithoutType (var (tRepr v) ty)

-- | Parser para propiedades.
parseProp :: ParserD ()
parseProp = do
            name <- parseName
            e <- parseExpr Nothing tryNewline
            st <- getState
            putState (st {pDecls = envAddProp (pDecls st) (Prop name e)})

-- | Parser de declaraciones.
parseDecl :: ParserD ()
parseDecl =  parseLet "spec" parseSpec
         <|> parseLet "prop" parseProp
         <|> parseBeginProof parseThm
         <|> parseLet "fun"  parseFun
         <|> parseLet "val"  parseVal

parseFromStringDecl :: String -> Either ParseError ()
parseFromStringDecl = runParser parseDecl initPState ""

-- | Estado inicial del parser.
initPState :: PDeclState
initPState = PDeclState { pDecls = initDeclarations
                        , pVarTy = EquP.initPExprState
                        , pProofs = EquP.initPProofState
                        }
