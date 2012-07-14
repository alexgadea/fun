
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
    show m = unlines [ "\n========LoadModule========="
                     , "ModName: " ++ show (modName m)
                     , "Imports: " ++ show (imports m)
                     , ""
                     , "Decls: " ++ show (decls m)
                     , ""
                     , "Derivations: " ++ show (derivations m)
                     , "=========================="
                     ]

data Import = Import ModName
    deriving (Eq, Show)

addDerivationsModule :: Module -> Module
addDerivationsModule m = m {derivations = createDerivations (decls m)} 
