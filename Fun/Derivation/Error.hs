module Fun.Derivation.Error where

-- | Errores sobre las derivaciones.
data DerivationError = DerError
    deriving Eq

instance Show DerivationError where
    show DerError =  "Error no especificado."   
