module Fun.Environment where

import Fun.Module
import Fun.Module.Error
import Fun.Parser
import Fun.Parser.Internal
import Fun.Parser.Module
import Fun.Decl(FunDecl)
import Fun.Declarations
import Fun.Derivation

import Data.Either (lefts)
import qualified Data.List as L (map,elem,filter,notElem,nub)
import Data.Text (unpack,pack)

import Control.Applicative ((<$>))
import Control.Arrow ((***))
import Control.Monad (foldM)
import Control.Monad.Identity  
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State (StateT,get,put,runStateT,modify)

import Prelude hiding (catch)
import qualified Control.Exception as C
import IO

-- | Environment es el conjunto de módulos que se tienen cargados en un momento dado
--   en Fun. Cada vez que se hace un import desde un módulo, debe referirse a un
--   módulo que se encuentre en el environment.
type Environment = [Module]

data ImportedModule = ImportedModule { imodName :: ModName
                                     , importPath :: [ModName]
                                     }

instance Show ImportedModule where
    show im = unlines [ "\n========ImportInfo========="
                      , "imodName: " ++ show (imodName im) 
                      , "importPath: " ++ show (importPath im)
                      , "==========================="
                      ]

instance Eq ImportedModule where
    im == im' = imodName im == imodName im'

type ImModuleList = [ImportedModule]

type StateCM = (ImModuleList,Environment)

type CheckModule a = StateT StateCM IO a

initStateCM :: StateCM
initStateCM = ([],[])

addModuleEnv :: Module -> Environment -> Environment
addModuleEnv = (:)

addImportedModule :: ModName -> [ModName] -> ImModuleList -> ImModuleList
addImportedModule mn mns ims = ImportedModule mn mns : imsUpdate
    where
        imsUpdate :: ImModuleList
        imsUpdate = L.map (extendIms mn) ims
        extendIms :: ModName -> ImportedModule -> ImportedModule
        extendIms mn im = if mn `L.elem` importPath im
                            then im {importPath = L.nub $ mns ++ importPath im}
                            else im

checkImports :: ModName -> [ModName] -> ImModuleList -> Bool
checkImports mn mns = foldl (\b im -> b && 
                                if mn `L.elem` importPath im
                                    then imodName im `L.notElem` mns
                                    else True) True

checkModule :: Module -> CheckModule (Maybe ModuleError)
checkModule m = do
    st <- get
    if m `L.elem` snd st 
        then return Nothing 
        else do

    
    let mImports = L.map (\(Import mn) -> mn) $ imports m
    let msWithm = addImportedModule (modName m) mImports $ fst st
    
    let cycleTest = not $ checkImports (modName m) mImports msWithm
        
    if cycleTest 
       then return . Just $ ModuleCycleImport $ L.map imodName msWithm 
       else do
    
    put (msWithm, snd st)
    isValidLoad <- loadModules mImports
    
    if isValidLoad /= Nothing 
        then return isValidLoad 
        else do
    
    env <- snd <$> get

    let moduleDecls = extractDeclImported m env
    
    let invalidSpec = lefts $ checkSpecs moduleDecls
    let invalidFuns = lefts $ checkFuns  moduleDecls
    let invalidVals = lefts $ checkVals  moduleDecls
    let invalidThm  = lefts $ checkThm   moduleDecls
    let invalidDers = lefts $ L.map checkDerivation $ derivations m

    case (invalidSpec, invalidFuns, invalidVals, invalidThm, invalidDers) of
        ([],[],[],[],[]) -> modify (id *** addModuleEnv m) >> return Nothing
        mErrs -> return . Just $ createError (modName m) mErrs

extractDeclImported :: Module -> Environment -> Declarations
extractDeclImported m env = 
            foldl concatDeclarations (decls m) imDecls
    where
        imMods :: Module -> [Module]
        imMods m = L.filter (\m' -> Import (modName m') `L.elem` imports m) env
        imMods' :: Module -> [Module]
        imMods' m = foldl (\l m' -> 
                            if m' `L.elem` l
                                then []
                                else l ++ imMods m' ++ imMods' m') [] (imMods m)
        imDecls :: [Declarations]
        imDecls = L.map decls $ imMods m ++ imMods' m

parseFromFileModule :: TextFilePath -> IO (Either ModuleError Module)
parseFromFileModule fp = readModule (unpack fp) >>= \eitherS ->
                        either (return . Left) (return . load) eitherS
    where
        load :: String -> Either ModuleError Module
        load s = case (parseFromStringModule s) of
                    Left err -> Left $ ModuleParseError err
                    Right m -> Right m
        readModule :: FilePath -> IO (Either ModuleError String)
        readModule fp =
                    (C.catch (readFile fp)
                             (\e -> do 
                                    let err = show (e :: C.IOException) 
                                    return "ModuleError")) >>= \eErr ->
                    case eErr of
                        "ModuleError" -> return $ Left $ ModuleErrorFileDoesntExist $ pack fp
                        _ -> return $ Right eErr

loadModules :: [ModName] -> CheckModule (Maybe ModuleError)
loadModules = foldM (\may mn -> let mnf = (unpack mn) ++ ".fun" in
                case may of
                    Just merr -> return $ Just merr
                    _-> do
                        mParsedM <- liftIO $ parseFromFileModule (pack mnf)
                        either (return . Just) checkModule mParsedM) Nothing

loadMainModule :: ModName -> IO (Either ModuleError Environment)
loadMainModule mod = do
       mParsedM <- liftIO $ parseFromFileModule mod
       either (return . Left) 
              (\m -> do
                (mErr,st) <- runStateT (checkModule m) initStateCM 
                maybe (return $ Right $ snd st) (return . Left) mErr
              ) mParsedM

loadMainModuleFromString :: String -> IO (Either ModuleError (Environment,ModName))
loadMainModuleFromString s = do
       let mParsedM = parseFromStringModule s
       either (return . Left . ModuleParseError) 
              (\m -> do
                (mErr,st) <- runStateT (checkModule m) initStateCM 
                maybe (return $ Right (snd st,modName m)) (return . Left) mErr
              ) mParsedM

-- Queries for environments
getFuncs :: Environment -> [FunDecl]
getFuncs = concatMap (map snd . functions . decls)
