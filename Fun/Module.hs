
module Fun.Module where

import Fun.Decl
import Data.Text

type ModName = Text

data Module = Module {
                modName :: ModName 
              , imports :: [Import]
              , decls   :: [Decl]
            }
    deriving Show

data Import = Import ModName
    deriving Show
