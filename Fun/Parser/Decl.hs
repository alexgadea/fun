-- | Este modulo es el parser de declaraciones.
module Fun.Parser.Decl where

-- Imports de EQU.
import Equ.Syntax(var, tRepr,Variable,VarName,FuncName,Func(..))
import Equ.Parser(Parser',parsePreExpr,parseTyFromString)
import qualified Equ.PreExpr as PE ( PreExpr, PreExpr' (Var), PreExpr' (Fun)
                                   , toFocus,Focus,unParen
                                   , listOfVar,listOfFun
                                   , toExpr
                                   )
import Equ.Types(Type, tyVarInternal)
import Equ.Proof (validateProof, printProof)
import Equ.Proof.Proof ( Proof'(..)
                       , Ctx
                       , Basic (..) 
                       , Theorem (..)
                       , Axiom (..)
                       , getEnd 
                       , getStart
                       , beginCtx
                       , Proof)
import Equ.Theories (theories,axiomGroup,TheoryName,createTheorem)
import Equ.Rule hiding (rel)

-- Imports de Parsec.
import Text.Parsec
import Text.Parsec.Error
import Text.Parsec.Token
import Text.Parsec.Language(emptyDef)

-- Imports Data.*
import Data.Text(Text,pack)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M (empty,Map,member,insert,(!)) 

-- Imports Monad.
import Control.Monad.Identity (unless, Identity)
import Control.Applicative ((<$>),(<*>))

-- Imports Fun.
import Fun.Decl
import Fun.Environment

type EitherName = Either VarName FuncName

type VarTy = (Int,M.Map EitherName Type)

data PState = PState { pEnv :: Environment
                     , pVarTy :: VarTy
                     }

type ParserD a = ParsecT String PState Identity a

lexer = lexer' { whiteSpace = oneOf " \t" >> return ()}
    where
        lexer' :: TokenParser PState
        lexer' = makeTokenParser $ 
                    emptyDef { reservedNames = rNames
                             , identStart  = alphaNum <|> char '_'
                             , identLetter = alphaNum <|> char '_'
                             , caseSensitive = True
                             }

-- | Nombres reservados de las declaraciones. 
rNames :: [String]
rNames = [ "let", "fun", "spec"
         , "thm", "prop", "val"
         , ":", "="
         ]

keyword :: String -> ParserD ()
keyword  = reserved lexer

keywordLet :: ParserD ()
keywordLet = keyword "let"

whites :: ParserD ()
whites = whiteSpace lexer 

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
parseExpr :: Maybe [Variable] -> ParserD PE.PreExpr
parseExpr mvs = getState >>= \st ->
            fmap (exprL $ pVarTy st) (manyTill anyChar (try (char '\n'))) >>= 
            pass
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
parseLet s p = try (keywordLet >> keyword s >> p)

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
            Maybe (PE.PreExpr -> Bool) -> ParserD Decl
parseSF cnstr mfun = parseFuncPreExpr >>= \fun -> 
            parseFunWithType fun <|> parseFunWithoutType fun
    where
        parseFunWithoutType :: Func -> ParserD Decl
        parseFunWithoutType fun = do
                    let is = fromMaybe (const True) mfun
                    vs <- parseFunArgs
                    e <- parseExpr (Just vs)
                    st <- getState
                    case (is e, M.member fun $ functions $ pEnv st) of
                        (False,_) -> fail "La expresión no es un programa."
                        (_,True) -> fail "Doble declaración de una función."
                        _ -> putState (st {pEnv = envAddFun (pEnv st) fun e}) >> 
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
parseSpec = parseSF Spec Nothing

-- | Parsea una función.
parseFun :: ParserD Decl
parseFun = parseSF Fun $ Just isPrg

-- | Pasea un teorema, evidentemente todavía no lo hace :D
parseThm :: ParserD Decl
parseThm = undefined 

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
                keyword "=" >> parseExpr Nothing >>= \e ->
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
parseProp = parseName >>= \name -> parseExpr Nothing >>= 
            \e -> return (Prop name e)

-- | Parser de declaraciones.
parseDecl :: ParserD Decl
parseDecl =  parseLet "spec" parseSpec -- Ya esta.
         <|> parseLet "prop" parseProp -- Ya esta.
         <|> parseLet "thm"  parseThm
         <|> parseLet "fun"  parseFun -- Ya esta.
         <|> parseLet "val"  parseVal -- Ya esta.

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
