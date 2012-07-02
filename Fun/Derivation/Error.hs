module Fun.Derivation.Error where

import Equ.Proof


-- | Errores sobre las derivaciones.
data DerivationError = 
                  InvalidSpec -- La declaración de especificación no es una especificación válida.
                | InvalidPrg  -- La declaración de programa no es un programa válido.
                | NotEqualFun -- La especificación y el programa corresponden a distintas funciones. 
                | DerivationProof ProofError -- La prueba de la derivación no es válida
    deriving Eq
    
    
instance Show DerivationError where
    show InvalidSpec = "La declaración de especificación no es una especificación válida"
    show InvalidPrg = "La declaración de programa no es un programa válido"
    show NotEqualFun = "La especificación y el programa corresponden a distintas funciones"
    show (DerivationProof perror) = "La prueba de derivación no es válida: "++ show perror