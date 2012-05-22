{-# Language OverloadedStrings #-}
module Fun.FunTypes.Nat where

import Equ.Theories.Arith
import Equ.Types

import Fun.IndTypes

import Data.Maybe(fromJust)


-- Los tipos inductivos los construimos nosotros programadores, pongo fromJust
-- para que si cometemos un error al crear un tipo inductivo, salte a la vista.
natural :: IndType
natural = fromJust $ createIndType "Natural" (TyAtom ATyNat) [natZero] [natSucc]
