module Fun.Environment where

import Fun.Module
import Fun.Module.Error
import Fun.Parser
import Fun.Parser.Internal
import Fun.Parser.Module
import Fun.Declarations
import Fun.Derivation

import Data.Either (lefts)
import qualified Data.List as L (map,elem,filter)
import Data.Text (unpack,pack)

import Control.Monad (foldM)
import Control.Monad.Identity  
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State (StateT,get,put,runStateT)

-- | Environment es el conjunto de módulos que se tienen cargados en un momento dado
--   en Fun. Cada vez que se hace un import desde un módulo, debe referirse a un
--   módulo que se encuentre en el environment.
type Environment = [Module]

data ImportedModule = ImportedModule { imodName :: ModName
                                     , importPath :: [ModName]
                                     }

instance Show ImportedModule where
    show im = unlines [ "========ImportInfo========="
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
addImportedModule mn mns ims = ImportedModule mn mns : ims

checkImports :: ModName -> [ModName] -> ImModuleList -> Bool
checkImports mn mns ims = foldl (\b im -> b && 
                                if mn `L.elem` (importPath im)
                                    then not $ (imodName im) `L.elem` mns
                                    else True) True ims

checkModule :: Module -> CheckModule (Maybe ModuleError)
checkModule m = do
    st <- get
    if m `L.elem` snd st then return Nothing
    else do
    
    let mImports = L.map (\(Import mn) -> mn) $ imports m
    let msWithm = addImportedModule (modName m) mImports $ fst st
    
    let cycleTest = not $ checkImports (modName m) mImports msWithm
    if cycleTest then return . Just $ ModuleCycleImport $ L.map (imodName) msWithm
    else do
    
    put (msWithm, snd st)
    isValidLoad <- loadModules mImports
    
    if isValidLoad /= Nothing then return isValidLoad
    else do
    
    env <- get >>= return . snd
    let moduleDecls = extractDeclImported m env
    
    let invalidSpec = lefts $ checkSpecs moduleDecls
    let invalidFuns = lefts $ checkFuns  moduleDecls
    let invalidVals = lefts $ checkVals  moduleDecls
    let invalidThm  = lefts $ checkThm   moduleDecls
    let invalidDers = concat $ lefts $ L.map checkDerivation $ derivations m
    case (invalidSpec, invalidFuns, invalidVals, invalidThm, invalidDers) of
        ([],[],[],[],[]) -> 
                    get >>= \(mns,env) -> 
                    put (mns, addModuleEnv (addDerivationsModule m) env) >>
                    return Nothing
        mErrs -> return . Just $ createError (modName m) mErrs

extractDeclImported :: Module -> Environment -> Declarations
extractDeclImported m env = 
            foldl concatDeclarations (decls m) imDecls
    where
        imMods :: Module -> [Module]
        imMods m = L.filter (\m' -> Import (modName m') `L.elem` imports m) env
        imMods' :: Module -> [Module]
        imMods' m = foldl (\l m' -> if m' `L.elem` l
                                       then []
                                       else l ++ imMods m' ++ imMods' m') [] (imMods m)
        imDecls :: [Declarations]
        imDecls = L.map decls $ imMods m ++ imMods' m
                  

parseFromFileModule :: TextFilePath -> IO (Either ModuleError Module)
parseFromFileModule fp = readFile ("ModuleExamples/" ++ (unpack fp)) >>= \s ->
                        case parseFromStringModule s of
                            Left err -> return . Left $ ModuleParseError err
                            Right m -> return $ Right m

loadModules :: [ModName] -> CheckModule (Maybe ModuleError)
loadModules mns = foldM (
                \may mn -> 
                case may of
                    Just merr -> return $ Just merr
                    _-> do
                        mParsedM <- liftIO $ parseFromFileModule mn
                        either (return . Just) checkModule mParsedM) Nothing mns

testModule :: IO (Either ModuleError (Maybe ModuleError, StateCM))
testModule = do
       mParsedM <- liftIO $ parseFromFileModule $ pack "TestModule"
       either (return . Left) 
              (\m -> do
                res <- runStateT (checkModule m) initStateCM 
                return $ Right res
              ) mParsedM
