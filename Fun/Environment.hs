module Fun.Environment where

import Fun.Module
import Fun.Module.Error
import Fun.Parser
import Fun.Parser.Internal
import Fun.Parser.Module
import Fun.Declarations
import Fun.Derivation

import Data.Either (lefts)
import Data.List as L (map)
import Data.Text (unpack,pack)

import Control.Monad (foldM)
import Control.Monad.Identity  
import Control.Monad.IO.Class (liftIO)
import Control.Monad.State (StateT,get,put,runStateT)

-- | Environment es el conjunto de módulos que se tienen cargados en un momento dado
--   en Fun. Cada vez que se hace un import desde un módulo, debe referirse a un
--   módulo que se encuentre en el environment.
type Environment = [Module]

type ModNameList = [ModName]

type StateCM = (ModNameList,Environment)

type CheckModule a = StateT StateCM IO a

initStateCM :: StateCM
initStateCM = ([],[])

addModuleEnv :: Module -> Environment -> Environment
addModuleEnv m env = m : env

checkModule :: Module -> CheckModule (Maybe ModuleError)
checkModule m = do
        let mImports = imports m
        
        isValidLoad <- loadModules $ L.map (\(Import mn) -> mn) mImports
        
        if isValidLoad /= Nothing then return isValidLoad
        else do
        
        let invalidSpec = lefts $ checkSpecs $ decls m
        let invalidFuns = lefts $ checkFuns $ decls m
        let invalidVals = lefts $ checkVals $ decls m
        let invalidThm  = lefts $ checkThm $ decls m
        let invalidDers = concat $ lefts $ L.map checkDerivation $ derivations m
        case (invalidSpec, invalidFuns, invalidVals, invalidThm, invalidDers) of
            ([],[],[],[],[]) -> 
                        get >>= \(mns,env) -> 
                        put (mns, addModuleEnv (addDerivationsModule m) env) >>
                        return Nothing
            mErrs -> return . Just $ createError mErrs

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
