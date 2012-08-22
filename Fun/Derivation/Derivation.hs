module Fun.Derivation.Derivation where

import Fun.Decl
import Fun.Derivation.Error
import Fun.Decl.Error

-- | Una derivación contiene una especificación, un programa y la prueba
--   de que ambos son equivalentes.
data Derivation = Derivation { deriv :: DerivDecl
                             , derivPos :: DeclPos
                             , spec :: SpecDecl
                             , prog :: Maybe FunDecl
                             }
    deriving Eq

instance Show Derivation where
    show d = "\n\nDerivación\nSpec: " ++ show (spec d) ++
             "\nDeriv: " ++ show (deriv d) ++
             "\nProg: " ++ show (prog d)
             
             
type EDeriv' a = Either ([DerivationError], DerivDecl) a
type EDeriv = EDeriv' Derivation
             
whenDer :: Bool -> ([DerivationError],DerivDecl) -> EDeriv' ()
whenDer b e | b = return ()
            | otherwise = Left e