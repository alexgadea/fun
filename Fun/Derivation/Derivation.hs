module Fun.Derivation.Derivation where

import Fun.Decl

import Equ.Proof

-- | Una derivación contiene una especificación, un programa y la prueba
--   de que ambos son equivalentes.
data Derivation = Derivation { spec :: SpecDecl
                             , prog :: FunDecl
                             , proof :: Proof
                             }
    deriving Eq

instance Show Derivation where
    show d = "\n\nDeriv\nSpec: " ++ show (spec d) ++
             "\nProg: " ++ show (prog d) ++
             "\nProof: " ++ show (proof d)
