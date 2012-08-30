-- | Definimos la noción de módulo de fun.
module Fun.Module where

import Fun.Verification
import Fun.Declarations
import Fun.Derivation

import Data.Text (Text)

type ModName = Text

data Module = Module { modName       :: ModName
                     , imports       :: [Import]
                     , decls         :: Declarations
                     , verifications :: [Verification]
                     , derivations   :: [Derivation]
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
                     , "Verifications : " ++ show (verifications m)
                     , "=========================="
                     ]

data Import = Import ModName
    deriving (Eq, Show)

modifyFunDeclMod f m = m { decls = modifyFunDecl f (decls m) }

