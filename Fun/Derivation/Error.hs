module Fun.Derivation.Error where

import Equ.PreExpr
import Equ.Proof
import Data.Text

type ErrInDeriv d = ([DerivationError],d)

-- | Errores sobre las derivaciones.
data DerivationError =   InvalidVariable Variable
                       | NotSpecification
                       | RedefinedDerivation Text
                       | ProofNotValid ProofError
    deriving Eq

instance Show DerivationError where
    show (InvalidVariable var) = 
            "La variable de la derivación debe ser la misma que en la especificación "
    show NotSpecification = "No existe la especificación correspondiente a esta derivación"
    show (RedefinedDerivation v) = "Ya hay una derivación de la función "++show v
    show (ProofNotValid perror) = "Error en la prueba de la derivación: "++ show perror 
