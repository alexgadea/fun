-- | Representación de errores para declaraciones.
module Fun.Decl.Error where

import Equ.Syntax
import Equ.Proof

import Data.Text (Text,unpack)

type ErrInDecl d = ([DeclError],d)

-- | Errores sobre las declaraciones.
data DeclError = UndeclaredVar Variable
               | UndeclaredFunc Func
               | InvalidPrgDeclaration
               | InvalidProofForThm ProofError
               | MultipleDeclaredVar Variable
               | MultipleDeclaredFunc Func
               | MultipleDeclaredSpec Func
               | MultipleDeclaredThm Text
               | MultipleDeclaredProp Text
    deriving Eq
    
instance Show DeclError where
    show (UndeclaredVar v) = "Variable " ++ show v ++ " sin declarar."
    show (UndeclaredFunc f) = "Función " ++ show f ++ " sin declarar."
    show InvalidPrgDeclaration = "La función no declara un programa valido."
    show (InvalidProofForThm perr) = "Prueba invalida: " ++ show perr
    show (MultipleDeclaredVar v) = "Multiple declaración de la varible " ++ show v
    show (MultipleDeclaredFunc f) = "Multiple declaración de la función " ++ show f
    show (MultipleDeclaredSpec s) = "Multiple declaración de la especificación " ++ show s
    show (MultipleDeclaredThm t) = "Multiple declaración de la teorema " ++ show (unpack t)
    show (MultipleDeclaredProp t) = "Multiple declaración de la proposición " ++ show (unpack t)
