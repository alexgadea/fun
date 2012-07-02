module Fun.Derivation.Derivation where

import Fun.Decl

import Equ.Proof

import Data.Text hiding (map)



-- | Una derivación contiene una especificación, un programa y la prueba
--   de que ambos son equivalentes.
data Derivation = Derivation {
                    espec :: Decl
                  , prog :: Decl
                  , proof :: Proof
                }
