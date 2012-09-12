-- | Environment es el conjunto de módulos que se tienen cargados en un momento dado
--   en Fun. Cada vez que se hace un import desde un módulo, debe referirse a un
--   módulo que se encuentre en el environment.
{-# Language DoAndIfThenElse #-}
module Fun.Environment where

import Fun.Module
import Fun.Module.Graph
import Fun.Module.Error
import Fun.Parser 
import Fun.Parser.Internal
import Fun.Parser.Module
import Fun.Decl(FunDecl)
import Fun.Declarations
import Fun.Verification
import Fun.Derivation
import Fun.TypeChecker

import Data.Either (lefts,rights,partitionEithers)
import qualified Data.List as L (map,elem,filter,notElem,nub)
import Data.Text (unpack,pack)
import Data.Graph.Inductive
import Data.Graph.Inductive.Query.DFS (reachable)

import Data.Maybe


import Control.Applicative ((<$>))
import Control.Arrow ((***),second)
import Control.Monad (foldM)
import Data.Functor.Identity
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.State

import Prelude hiding (catch)
import qualified Control.Exception as C
import System.IO

type Environment = [Module]

data StateCM = StateCM { imMGraph   :: ImModuleGraph
                       , modulesEnv :: Environment
                       }
    deriving Show

type CheckModule a = StateT StateCM IO a

initStateCM :: ImModuleGraph -> Environment -> StateCM
initStateCM = StateCM

-- No usar este añadir si se quiere actualizar el módulo.
addModuleEnv :: Module -> Environment -> Environment
addModuleEnv m env = if m `elem` env 
                        then env
                        else m : env

-- | Chequea la lista de módulos en el environment.
checkEnvModules :: CheckModule (Maybe ModuleError)
checkEnvModules = do
            st <- get
            foldM (\may m -> 
                    case may of
                        Just merr -> return $ Just merr
                        Nothing -> checkModule m
                  ) Nothing $ modulesEnv st

-- | Chequea una módulo del environment.
checkModule :: Module -> CheckModule (Maybe ModuleError)
checkModule m = do
    env <- modulesEnv <$> get
    imGraph <- imMGraph <$> get
    
    let rImports = reachableImports (modName m) imGraph
    let mImports = filter (\m -> modName m `elem` rImports) env
    
    let mImportedDecls = if null mImports
                            then Nothing
                            else Just $ foldr1 concatDeclarations 
                                      $ map validDecls mImports
    
    let invalidSpec = lefts $ checkSpecs (validDecls m) mImportedDecls
    let invalidFuns = lefts $ checkFuns  (validDecls m) mImportedDecls
    let invalidVals = lefts $ checkVals  (validDecls m) mImportedDecls
        
    let thmsCheck = checkThm   (validDecls m) mImportedDecls
    let invalidThm  = lefts thmsCheck
    -- buscamos las derivaciones. Si hay derivaciones sin especificación, o
    -- derivaciones repetidas, entonces la lista eDerivs tendrá errores de derivación.
    let eDerivs = createDerivations (validDecls m)
        
    
    let validThms = (rights thmsCheck) ++ (imThms mImportedDecls)
    let checkedDerivs = partitionEithers $ 
             L.map (checkDerivation (validDecls m) mImportedDecls validThms) eDerivs
    
    let eVerifs = createVerifications (validDecls m) mImportedDecls
    let checkedVerifs = partitionEithers $ L.map checkVerification eVerifs
    
    let inDeclarations = InvalidDeclarations [] [] 
                                             invalidThm 
                                             [] [] 
                                             (fst checkedDerivs)
    
    case (invalidSpec, invalidFuns, invalidVals, invalidThm, checkedVerifs,checkedDerivs) of
        ([],[],[],_,(inverifs,cverifs),(_,cderivs)) ->
            -- Agregamos al modulo las definiciones de funciones derivadas
            -- let m' = m { decls = (decls m) {functions = functions (decls m) ++ cderivs}
            --            , verifications = cverifs
            --            }
            let m' = m { validDecls = updateValidDecls (validDecls m) inDeclarations cderivs
                       , verifications = cverifs
                       , invalidDecls = InvalidDeclsAndVerifs inDeclarations inverifs
                       }
                funcs = functions . validDecls $ m'
            in
            case typeCheckDeclarations (map snd funcs) of
               Left e -> liftIO (putStrLn (show e)) >>
                        return (Just $ createError (modName m) ([],[],[],[],[],[]))
               Right funcs' -> let m' = m {validDecls = (validDecls m) { functions = zipWith (\(a,_) f -> (a,f)) funcs funcs' }}
                              in updateModuleEnv m' >> return Nothing

        (e1,e2,e3,e4,(e5,_),(e6,_)) -> 
            return . Just $ createError (modName m) (e1,e2,e3,e4,e5,e6)
    where
        updateValidDecls vd ind nf = filterVD {functions = filterVDFuncs ++ nf}
            where 
                filterVDFuncs = functions $ filterVD 
                filterVD = filterValidDecls vd ind
        updateModuleEnv :: Module -> CheckModule (Maybe ModuleError)
        updateModuleEnv m = do
                        modify (\s -> s { modulesEnv = map update $ modulesEnv s })
                        return Nothing
            where
                update :: Module -> Module
                update m' = if m == m' then m else m'
                
        imThms imds = maybe [] (map snd . theorems) imds

--             let funcs = functions moduleDecls ++ cderivs
-- --                m' = m {decls = (decls m) { functions = funcs }}

--             case typeCheckDeclarations (map snd funcs) of
--               Left _ -> return . Just $ createError (modName m) ([],[],[],[],[],[])
--               Right funcs' -> let m' = m {decls = (decls m) { functions = zipWith (\(a,_) f -> (a,f)) funcs funcs' }}
--                              in modify (second $ addModuleEnv m') >> return Nothing

-- | Dado un nombre de módulo, comienza la carga buscado en el archivo
-- correspondiente al módulo.
loadMainModule :: ModName -> IO (Either ModuleError Environment)
loadMainModule modN = do
       mParsedM <- liftIO $ parseFromFileModule modN
       either (return . Left) 
              (\m -> do
                let initCM = initStateCM (insModuleImports m emptyImMG) [m]
                (mErr,st) <- runStateT (loadAndCheck m) initCM
                maybe (return $ Right $ modulesEnv st) (return . Left) mErr
              ) mParsedM
    where loadAndCheck :: Module -> CheckModule (Maybe ModuleError)
          loadAndCheck m = loadEnv m >>= maybe checkEnvModules (return . Just)


-- | Carga los módulos en al environment, esto implica parsear el módulo inicial
-- y cargarlo, así como los imports en cadena.
loadEnv :: Module -> CheckModule (Maybe ModuleError)
loadEnv m = foldM (\ may (Import mn) -> 
                let mnf = unpack mn ++ ".fun" in
                case may of
                    Just merr -> return $ Just merr
                    _-> do
                        mParsedM <- liftIO $ parseFromFileModule (pack mnf)
                        either (return . Just) loadEnv' mParsedM
                  ) Nothing $ imports m
    where
        loadEnv' :: Module -> CheckModule (Maybe ModuleError)
        loadEnv' m = updateEnv m >> checkCycle >>= maybe (loadEnv m) (return . Just)
        checkCycle :: CheckModule (Maybe ModuleError)
        checkCycle = do
                    st <- get
                    let cycleList = filter ((>1) . length) . scc $ imMGraph st
                    if cycleList == []
                       then return Nothing
                       else return . Just $ ModuleCycleImport $ map (pack.show) $ head cycleList
        updateEnv :: Module -> CheckModule (Maybe ModuleError)
        updateEnv m = do
                    modify (\s -> s { imMGraph = insModuleImports m $ imMGraph s
                                    , modulesEnv = addModuleEnv m $ modulesEnv s
                                    })
                    return Nothing

-- Queries for environments
getFuncs :: Environment -> [FunDecl]
getFuncs = concatMap (map snd . functions . validDecls)

-- | Parsea una módulo en base a una dirección de archivo.
parseFromFileModule :: TextFilePath -> IO (Either ModuleError Module)
parseFromFileModule fp = readModule (unpack fp) >>= \eitherS ->
                        either (return . Left) (return . load) eitherS
    where
        load :: String -> Either ModuleError Module
        load = either (Left . ModuleParseError (pack "")) Right . parseFromStringModule 

readModule :: FilePath -> IO (Either ModuleError String)
readModule fp = C.catch (readFile fp)
                (\e -> do let err = show (e :: C.IOException)  in
                             return "ModuleError") >>= \eErr ->
                case eErr of
                  "ModuleError" -> return $ Left $ ModuleErrorFileDoesntExist $ pack fp
                  _ -> return $ Right eErr

loadMainModuleFromFile :: TextFilePath -> IO (Either ModuleError (Environment,ModName))
loadMainModuleFromFile fp = do
       mParsedM <- parseFromFileModule fp
       either (return . Left) 
              (\m -> do
                let initCM = initStateCM (insModuleImports m emptyImMG) [m]
                (mErr,st) <- runStateT (loadAndCheck m) initCM
                maybe (return $ Right (modulesEnv st,modName m)) (return . Left) mErr
              ) mParsedM
    where
        loadAndCheck :: Module -> CheckModule (Maybe ModuleError)
        loadAndCheck m = loadEnv m >>= maybe checkEnvModules (return . Just)

-- | Parsea un módulo desde una string.
loadMainModuleFromString :: String -> IO (Either ModuleError (Environment,ModName))
loadMainModuleFromString s = do
       let mParsedM = parseFromStringModule s
       either (return . Left . ModuleParseError (pack "")) 
              (\m -> do
                let initCM = initStateCM (insModuleImports m emptyImMG) [m]
                (mErr,st) <- runStateT (loadAndCheck m) initCM
                maybe (return $ Right (modulesEnv st,modName m)) (return . Left) mErr
              ) mParsedM
    where
        loadAndCheck :: Module -> CheckModule (Maybe ModuleError)
        loadAndCheck m = loadEnv m >>= maybe checkEnvModules (return . Just)
