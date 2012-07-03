
module Fun.Module where

import Fun.Decl
import Fun.Declarations
import Fun.Derivation
import Data.Text

type ModName = Text

data Module = Module {
                modName :: ModName
              , imports :: [Import]
              , decls   :: Declarations
              , derivations :: [Derivation]
            }

data Import = Import ModName
    deriving Show

createDerivations :: Declarations -> [Derivation]
createDerivations _ = []
    
    
    
    
    