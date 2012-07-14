module Fun.Derivation.Error where

import Equ.PreExpr
import Equ.Expr

type ErrInDeriv d = ([DerivationError],d)

-- | Errores sobre las derivaciones.
data DerivationError = InvalidStartOfProof PreExpr PreExpr
                     | InvalidEndOfProof PreExpr PreExpr
                     | MissingSpecHypInProof Expr
    deriving Eq

instance Show DerivationError where
    show (InvalidStartOfProof eInF eInp) = 
            "La expresión incial " ++ show eInp ++ 
            " de la prueba no se corresponde la función " ++ show eInF
    show (InvalidEndOfProof eInF eInp) = 
            "La expresión final, " ++ show eInp ++ 
            " de la prueba no se corresponde con la definición de la función " 
            ++ show eInF
    show (MissingSpecHypInProof hyp) =
            "La prueba no contiene la hipotesis " ++ show hyp
