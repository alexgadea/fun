
module Fun.Derivation where

import Fun.Decl
import Fun.Derivation.Derivation
import Fun.Derivation.Monad
import Fun.Derivation.Error

import Equ.Proof

import Data.Text hiding (map)


-- | Funcion que dada una derivacion dice si es válida o no.
--   Probablemente despues le cambiemos el tipo a algo monádico.
validateDerivation :: Derivation -> DM Derivation
validateDerivation d =
    getEspecFun d >>= \efun -> getPrgFun d >>= \pfun ->
    whenDM' (efun == pfun) NotEqualFun >>
    getPrgExpr d >>= \pexpr -> 
    whenDM' (isPrg pexpr) InvalidPrg >>
    case validateProof (proof d) of
         Left perror -> Left (DerivationProof perror)
         Right _ -> Right d