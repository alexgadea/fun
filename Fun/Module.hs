
module Fun.Module where

import Fun.Declarations
import Fun.Derivation

import Data.Text (Text)

type ModName = Text

data Module = Module { modName :: ModName
                     , imports :: [Import]
                     , decls   :: Declarations
                     , derivations :: [Derivation]
                     }

instance Eq Module where
    m == m' = modName m == modName m'
            
instance Show Module where
    show m = "\n========LoadModule=====\nModName: " ++ show (modName m) ++
             "\nImports: " ++ show (imports m) ++
             "\n\nDecls: " ++ show (decls m) ++
             "\n\nDerivations: " ++ show (derivations m) ++
             "\n=========================="

data Import = Import ModName
    deriving (Eq, Show)

addDerivationsModule :: Module -> Module
addDerivationsModule m = m {derivations = createDerivations (decls m)} 
