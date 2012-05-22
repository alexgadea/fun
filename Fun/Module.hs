
module Fun.Module where

import Fun.Decl
import Data.Text

type ModName = Text

data Module = Module ModName [Import] [Decl]

data Import = Import Module


