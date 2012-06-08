-- | Este modulo es el parser de declaraciones.
module Fun.Parser.Decl where

-- Imports de EQU.
import Equ.Syntax(var, tRepr,Variable,VarName,FuncName,Func(..))
import Equ.Parser(Parser',parsePreExpr,parseTyFromString,rel,proof)
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
import Fun.Environment( Environment
                      , vals, functions, props, specs
                      , envAddFun, envAddVar, envAddProp, envAddSpec
                      , initEnvironment)
import Fun.Parser.Internal

-- | Calcula el tipo de una variable o funcion
setType :: Either VarName FuncName -> PState -> (PState,Type)
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

-- | Checkea la definición previa de variables y funciones para un focus.
-- TODO: Acá se puede hacer bastante para informar los errores.
checkPrevDef :: PE.Focus -> Maybe [Variable] -> ParserD ()
checkPrevDef f mvs = do
                checkPrevDefVar
                checkPrevDefFun
    where
        checkPrevDefVar :: ParserD ()
        checkPrevDefVar = do
            st <- getState
            let valsEnv = vals $ pEnv st
            let vs = maybe (const True) (flip elem) mvs
            mapM_ (\f@(PE.Var v,_) -> unless (M.member v valsEnv || vs v) $
                    fail $ "Variable " ++ show f ++ " sin declarar.") 
                    (PE.listOfVar f)
        checkPrevDefFun :: ParserD ()
        checkPrevDefFun = do
            st <- getState
            let funcsEnv = functions $ pEnv st
            mapM_ (\f@(PE.Fun fun,_) -> unless (M.member fun funcsEnv) $
                    fail $ "Función " ++ show f ++ " sin declarar.")
                    (PE.listOfFun f)

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
        n :: PState -> Int
        n = fst . pVarTy
        maps :: PState -> M.Map EitherName Type
        maps = snd . pVarTy
        ins :: PState -> EitherName -> Type -> M.Map EitherName Type
        ins st ename ty = M.insert ename ty (maps st)

-- | Uso del parser de una expresión definido en 'Equ.Parser.Expr'.
-- TODO Ale: No esta bonito como manejamos el pasaje de errores con pass
-- ademas pasa que tenemos que re-acomodar la posición del error.
-- Algo raro es que la posición de la linea siempre esta un lugar mas "adelante"
-- (Actualización) Tengo bastante avanzado en como solucionar esto y agregar
-- ademas mucha mas informacion sobre los errores de parseo.
parseExpr :: Maybe [Variable] -> ParserD () -> ParserD PE.PreExpr
parseExpr mvs till = getState >>= \st ->
                     fmap (exprL $ pVarTy st) (manyTill anyChar till) >>= pass
    where
        pass :: Either ParseError PE.Focus -> ParserD PE.PreExpr
        pass ef = case ef of
                    Right f -> checkPrevDef f mvs >> return (PE.toExpr f)
                    Left per -> getPosition >>= \p -> 
                                fail $ show $ flip setErrorPos per $
                                setSourceLine (errorPos per) (sourceLine p-1)
        exprL' :: Parser' PE.Focus
        exprL' = fmap (PE.toFocus . PE.unParen) (spaces >> parsePreExpr)
        exprL :: VarTy -> String -> Either ParseError PE.Focus
        exprL vt = runParser exprL' vt ""

-- | Parsea el tipo de una función.
parseFunType :: ParserD Type
parseFunType = parseType'

-- | Parsea el tipo de una variable.
parseVarType :: ParserD Type
parseVarType = parseType'

-- | Parser general de tipos.
parseType' :: ParserD Type
parseType' = fmap parseTyFromString (manyTill anyChar (try (char '\n'))) >>= pass
    where
        pass :: Either ParseError Type -> ParserD Type
        pass ef = case ef of
                    Right e -> return e
                    Left per -> getPosition >>= \p -> 
                                fail $ show $ flip setErrorPos per $
                                setSourceLine (errorPos per) (sourceLine p-1)

-- | Parsea prefijos de declaraciones y continua con p.
parseLet :: String -> ParserD Decl -> ParserD Decl
parseLet s parse = try $ do many newline
                            keywordLet
                            keyword s
                            decl <- parse
                            many newline
                            return decl

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
parseSF ::  (Func -> [Variable] -> PE.PreExpr -> Decl) -> 
            (Environment -> Func -> PE.PreExpr -> Environment) ->
            (Environment -> M.Map Func PE.PreExpr) ->
            Maybe (PE.PreExpr -> Bool) -> ParserD Decl
parseSF cnstr envAdd sfs mfun = parseFuncPreExpr >>= \fun -> 
            parseFunWithType fun <|> parseFunWithoutType fun
    where
        parseFunWithoutType :: Func -> ParserD Decl
        parseFunWithoutType fun = do
                    let is = fromMaybe (const True) mfun
                    vs <- parseFunArgs
                    e <- parseExpr (Just vs) tryNewline
                    st <- getState
                    case (is e, M.member fun $ sfs $ pEnv st) of
                        (False,_) -> fail "La expresión no es un programa."
                        (_,True) -> fail "Doble declaración de una función."
                        _ -> putState (st {pEnv = envAdd (pEnv st) fun e}) >> 
                                return (cnstr fun vs e)
        parseFunWithType :: Func -> ParserD Decl
        parseFunWithType fun = try $
                    keyword ":" >>
                    parseFunType >>= \ty -> 
                    updateTypeFun (Right $ tRepr fun) ty >>
                    parseFuncPreExpr >>= \fun' ->
                    if fun /= fun' 
                        then fail (show fun ++ " != " ++ show fun') 
                        else parseFunWithoutType fun'
        parseFunArgs :: ParserD [Variable]
        parseFunArgs = manyTill parseVar (try $ string "=")

-- | Parsea una especificación.
parseSpec :: ParserD Decl
parseSpec = parseSF Spec envAddSpec specs Nothing

-- | Parsea una función.
parseFun :: ParserD Decl
parseFun = parseSF Fun envAddFun functions $ Just isPrg

-- | Parser de relaciones en ParserD, parsea hasta un terminador till.
parseRel :: ParserD () -> ParserD Relation
parseRel till = fmap parseRel' (manyTill anyChar till) >>= pass
    where
        pass :: Either ParseError Relation -> ParserD Relation
        pass er = case er of
                    Right r -> return r
                    Left per -> getPosition >>= \p -> 
                                fail $ show $ flip setErrorPos per $
                                setSourceLine (errorPos per) (sourceLine p-1)
        parseRel' :: String -> Either ParseError Relation
        parseRel' = runParser rel initVarTy ""

-- | Parser de pruebas para parserD, parsea una prueba hasta el terminador till.
parseProof :: ParserD () -> ParserD Proof
parseProof till = fmap parseProof' (manyTill anyChar till) >>= pass
    where
        pass :: Either ParseError Proof -> ParserD Proof
        pass ep = case ep of
                    Right p -> return p
                    Left per -> getPosition >>= \p -> 
                                fail $ show $ flip setErrorPos per $
                                setSourceLine (errorPos per) (sourceLine p-1)
        parseProof' :: String -> Either ParseError Proof
        parseProof' = runParser proof initVarTy ""

-- | Parsea un teorema.
-- TODO: Mejorar el informe de errores.
parseThm :: ParserD Decl
parseThm = do
    name <- parseName
    ei <- parseExpr Nothing keywordDot
    rel <- parseRel keywordDot
    ef <- parseExpr Nothing keywordWith
    p <- parseProof keywordEnd
    let eip = PE.toExpr $ fromJust $ getStart p
    let relp = fromJust $ getRel p
    let efp = PE.toExpr $ fromJust $ getEnd p
    case (ei == eip, rel == relp, ef == efp) of
        (False,_,_) -> fail $ show ei ++ "!="  ++ show eip
        (_,False,_) -> fail $ show rel ++ "!=" ++  show relp
        (_,_,False) -> fail $ show ef ++ "!=" ++ show efp
        _ -> return $ Thm name rel ei ef p
           

-- | Parser para declaracion de valores.
{- | Comprobaciones al parsear:
    1. Un val no puede haber sido declarado antes con el mismo nombre.
    2. Las variables y funciones que esten en la expresión relacionada con la 
        func/spec deben estar declaradas antes.
-}
parseVal :: ParserD Decl
parseVal = parseVar >>= \v -> parseVarWithoutType v <|> parseVarWithType v
    where 
        parseVarWithoutType :: Variable -> ParserD Decl
        parseVarWithoutType v = try $
                keyword "=" >> parseExpr Nothing tryNewline >>= \e ->
                getState >>= \st -> 
                case (isPrg e, M.member v $ vals $ pEnv st) of
                    (False,_) -> fail "La expresión no es un programa."
                    (_,True) -> fail "Doble declaración de una variable."
                    _ -> putState (st {pEnv = envAddVar (pEnv st) v e}) >> 
                        return (Val v e)
        parseVarWithType :: Variable -> ParserD Decl
        parseVarWithType v = try $
                    keyword ":" >>
                    parseFunType >>= \ty -> 
                    updateTypeVar (Left $ tRepr v) ty >>
                    parseVar >>= \v' ->
                    if v /= v' 
                        then fail (show v ++ " != " ++ show v') 
                        else parseVarWithoutType (var (tRepr v) ty)

-- | Parser para propiedades.
parseProp :: ParserD Decl
parseProp = parseName >>= \name ->
            getState >>= \st -> 
            if M.member name $ props $ pEnv st
                then fail "Doble declaración de una propiedad."
                else parseExpr Nothing tryNewline >>= \e -> 
                     putState (st {pEnv = envAddProp (pEnv st) name e}) >> 
                     return (Prop name e)

-- | Parser de declaraciones.
parseDecl :: ParserD Decl
parseDecl =  parseLet "spec" parseSpec
         <|> parseLet "prop" parseProp
         <|> parseLet "thm"  parseThm
         <|> parseLet "fun"  parseFun
         <|> parseLet "val"  parseVal

parseFromStringDecl :: String -> Either ParseError Decl
parseFromStringDecl = runParser parseDecl initPState ""

-- | Estado inicial para la inferencia de tipos de variables y funciones.
initVarTy :: VarTy
initVarTy = (0,M.empty)

-- | Estado inicial del parser.
initPState :: PState
initPState = PState { pEnv = initEnvironment
                    , pVarTy = initVarTy
                    }
