-- | Environment es el conjunto de módulos que se tienen cargados en un momento dado
--   en Fun. Cada vez que se hace un import desde un módulo, debe referirse a un
--   módulo que se encuentre en el environment.
{-# Language DoAndIfThenElse,TemplateHaskell #-}
module Fun.Environment where

import Fun.Module
import Fun.Module.Graph
import Fun.Module.Error
import Fun.Parser 
import Fun.Decl(FunDecl,ValDecl)
import Fun.Declarations
import Fun.Verification
import Fun.Derivation
import Fun.TypeChecker

import Data.Either (lefts,rights,partitionEithers)
import qualified Data.List as L (map)
import Data.Text (unpack,pack)
import Data.Graph.Inductive
import Data.List(find)
import Data.Monoid(mconcat)
import System.FilePath.Posix

import Control.Lens
import Control.Monad (foldM)
import Control.Monad.IO.Class (liftIO)
import Control.Monad.Trans.State

import qualified Control.Exception as C

type Environment = [Module]

data StateCM = StateCM { _imMGraph   :: ImModuleGraph
                       , _modulesEnv :: Environment
                       }
    deriving Show

$(makeLenses ''StateCM)

type CheckModule a = StateT StateCM IO a

initStateCM :: ImModuleGraph -> Environment -> StateCM
initStateCM = StateCM

-- No usar este añadir si se quiere actualizar el módulo.
addModuleEnv :: Module -> Environment -> Environment
addModuleEnv m env = if m `elem` env then env else m : env

-- | Chequea la lista de módulos en el environment.
checkEnvModules :: CheckModule (Maybe ModuleError)
checkEnvModules = get >>= foldM proceed Nothing . (^. modulesEnv)
    where proceed so m = maybe (checkModule m) (return . Just) so

-- | Chequea un módulo del environment.
checkModule :: Module -> CheckModule (Maybe ModuleError)
checkModule m = do
    env     <- use modulesEnv 
    imGraph <- use imMGraph
    
    let rImports = reachableImports (modName m) imGraph
    let mImports = filter ((`elem` rImports) . modName) env
    
    let mImportedDecls = mconcat$ map validDecls mImports
    
    let invalidSpec = lefts $ checkSpecs (validDecls m) mImportedDecls
    let invalidFuns = lefts $ checkFuns  (validDecls m) mImportedDecls

    let invalidVals = lefts $ checkVals  (validDecls m) mImportedDecls
        
    let thmsCheck = checkThm (validDecls m) mImportedDecls
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
                funcs = _functions . validDecls $ m'
            in
            case typeCheckDeclarations (map snd funcs) of
               Left e -> liftIO (putStrLn (show e)) >>
                        return (Just $ createError (modName m) ([],[],[],[],[],[]))
               Right funcs' -> let m'' = m' {validDecls = (validDecls m') { _functions = zipWith (\(a,_) f -> (a,f)) funcs funcs' }}
                              in updateModuleEnv m'' >> return Nothing

        (e1,e2,e3,e4,(e5,_),(e6,_)) -> 
            return . Just $ createError (modName m) (e1,e2,e3,e4,e5,e6)
    where
        imThms imds = bareThms imds


updateValidDecls vd ind nf = over functions (++ nf) $ filterValidDecls vd ind 

updateModuleEnv :: Module -> CheckModule ()
updateModuleEnv m = modulesEnv %= map update
    where update :: Module -> Module
          update m' = if m == m' then m else m'

-- | Dado un nombre de módulo, comienza la carga buscado en el archivo
-- correspondiente al módulo.
loadMainModule :: FilePath -> ModName -> IO (Either ModuleError Environment)
loadMainModule path modN = do
       mParsedM <- liftIO $ parseFromFileModule modN
       either (return . Left) 
              (\m -> do
                let initCM = initStateCM (insModuleImports m emptyImMG) [m]
                (mErr,st) <- runStateT (loadAndCheck m) initCM
                maybe (return $ Right $ (^. modulesEnv) st) (return . Left) mErr
              ) mParsedM
    where loadAndCheck :: Module -> CheckModule (Maybe ModuleError)
          loadAndCheck m = loadEnv path m >>= maybe checkEnvModules (return . Just)


-- | Carga los módulos en al environment, esto implica parsear el módulo inicial
-- y cargarlo, así como los imports en cadena.
loadEnv :: FilePath -> Module -> CheckModule (Maybe ModuleError)
loadEnv path m = foldM (\ may (Import mn) -> 
                    let mnf = path ++ unpack mn ++ ".fun" in
                    case may of
                        Just merr -> return $ Just merr
                        _-> do
                            mParsedM <- liftIO $ parseFromFileModule (pack mnf)
                            either (return . Just) loadEnv' mParsedM
                    ) Nothing $ imports m
    where
        loadEnv' :: Module -> CheckModule (Maybe ModuleError)
        loadEnv' m = updateEnv m >> checkCycle >>= maybe (loadEnv path m) (return . Just)
        checkCycle :: CheckModule (Maybe ModuleError)
        checkCycle = do
                    graph <- use imMGraph
                    let cycleList = filter ((>1) . length) . scc $ graph
                    if cycleList == []
                       then return Nothing
                       else return . Just $ ModuleCycleImport $ map (pack.show) $ head cycleList
        updateEnv :: Module -> CheckModule ()
        updateEnv m = imMGraph   %= insModuleImports m >> 
                      modulesEnv %= addModuleEnv m

-- Queries for environments
getFuncs :: Environment -> [FunDecl]
getFuncs = concatMap (bare functions . validDecls)

getVals :: Environment -> [ValDecl]
getVals = concatMap (bare vals . validDecls)

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
                maybe (return $ Right (st ^. modulesEnv,modName m)) (return . Left) mErr
              ) mParsedM
    where
        loadAndCheck :: Module -> CheckModule (Maybe ModuleError)
        loadAndCheck m =
            let folder = (takeDirectory (unpack fp) ++ [pathSeparator]) in
                    loadEnv folder m >>= maybe checkEnvModules (return . Just)

getModule :: Environment -> ModName -> Maybe Module
getModule env mname = find ((== mname) . modName) env
        