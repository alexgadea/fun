-- | Definimos la noción de módulo de fun.
module Fun.Module where

import Fun.Verification
import Fun.Declarations
import Fun.Derivation

import Data.Text (Text)

type ModName = Text

data InvalidDeclsAndVerifs =  
        InvalidDeclsAndVerifs { decls  :: InvalidDeclarations
                              , verifs :: [ErrInVerif Verification]
                              }
    deriving Show
                            
data Module = Module { modName       :: ModName
                     , imports       :: [Import]
                     , validDecls    :: Declarations
                     , invalidDecls  :: InvalidDeclsAndVerifs
                     , verifications :: [Verification]
                     , derivations   :: [Derivation]
                     }

instance Eq Module where
    m == m' = modName m == modName m'

instance Show Module where
    show m = unlines [ ""
                     , "========LoadModule========="
                     , "ModName: " ++ show (modName m)
                     , "Imports: " ++ show (imports m)
                     , ""
                     , "Decls: " ++ show (validDecls m)
                     , ""
                     , "Verifications : " ++ show (verifications m)
                     , "Derivations : " ++ show (derivations m)
                     , "Invalid Decls : " ++ show (invalidDecls m)
                     , "=========================="
                     ]

data Import = Import ModName
    deriving (Eq, Show)


allDeclsValid :: Module -> Bool
allDeclsValid m = 
    let invd = decls (invalidDecls m) in
        inSpecs invd == [] && inFunctions invd == [] &&
        inTheorems invd == [] && inProps invd == [] &&
        inVals invd == [] && inVals invd == [] &&
        inDerivs invd == [] &&
        verifs (invalidDecls m) == []
    
    
    