-- | Representación de errores para declaraciones.
module Fun.Decl.Error where

import Equ.Syntax
import Equ.Proof

type ErrInDecl d = ([DeclError],d)

-- | Errores sobre las declaraciones.
data DeclError = UndeclaredVar Variable
               | UndeclaredFunc Func
               | InvalidPrgDeclaration
               | InvalidProofForThm ProofError
    deriving Eq
    
instance Show DeclError where
    show (UndeclaredVar v) = "Variable " ++ show v ++ " sin declarar."
    show (UndeclaredFunc f) = "Función " ++ show f ++ " sin declarar."
    show InvalidPrgDeclaration = "La función no declara un programa valido."
    show (InvalidProofForThm perr) = "Prueba invalida: " ++ show perr
