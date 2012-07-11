
module Fun.Derivation (
      Derivation(..)
    , module Fun.Derivation.Monad
    , module Fun.Derivation.Error
    , createDerivations
    , checkDerivation
    )
    where

import Fun.Decl
import Fun.Declarations
import Fun.Derivation.Derivation
import Fun.Derivation.Monad
import Fun.Derivation.Error

import Equ.Proof

import Data.Text hiding (map)
import Data.List as L (map, find)
import Data.Either (rights)
import Data.Maybe (fromJust)

createDerivations :: Declarations -> [Derivation]
createDerivations decls = do
                let vSpecs = rights $ checkSpecs decls
                let vFuns = rights $ checkFuns decls
                let vThm = rights $ checkThm decls
                let der = createDer vSpecs vFuns vThm
                L.map fromJust der
    where
        createDer :: [SpecDecl] -> [FunDecl] -> [ThmDecl] -> [Maybe Derivation]
        createDer specs funcs thms = 
            L.map (\s -> L.find (equalFun s) funcs >>= \f ->
                        L.find (equalThm f) thms >>= \(Thm theo) ->
                        Just (Derivation s f (thProof theo))) specs
        equalFun :: SpecDecl -> FunDecl -> Bool
        equalFun s f = getFuncDecl s == getFuncDecl f
        equalThm :: FunDecl -> ThmDecl -> Bool
        equalThm f t = (Just $ getThmName t) == getFunDerivingFrom f

-- | Funcion que dada una derivacion dice si es válida o no.
--   Probablemente despues le cambiemos el tipo a algo monádico.
checkDerivation :: Derivation -> DM Derivation
checkDerivation = return
--     getEspecFun d >>= \efun -> getPrgFun d >>= \pfun ->
--     whenDM' (efun == pfun) NotEqualFun >>
--     getPrgExpr d >>= \pexpr -> 
--     whenDM' (isPrg pexpr) InvalidPrg >>
--     case validateProof (proof d) of
--          Left perror -> Left (DerivationProof perror)
--          Right _ -> Right d