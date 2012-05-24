
module Fun.Decl where

import Equ.PreExpr
import Equ.Syntax
import Equ.Rule
import Equ.Proof
import Data.Text hiding (map)



{- Decl representa declaraciones en Fun. Una especificacion sera una pre-expresión
   en funcion de algunas teorias.
   Una funcion estará definida por una expresión que es ejecutable. No todas las expresiones
   cumplen esta propiedad, por lo que damos un predicado al respecto. -}
data Decl =   Spec Func [Variable] PreExpr
            | Prop Text PreExpr
            | Thm Text Relation PreExpr PreExpr Proof
            | Fun Func [Variable] PreExpr -- como hacemos con el derived from...?
            | Val Variable PreExpr
            
            

isPrg :: PreExpr -> Bool
isPrg (Quant _ _ _ _) = False
isPrg (PrExHole _) = False
isPrg (UnOp op pe) = isPrg pe
isPrg (BinOp op pe pe') = isPrg pe && isPrg pe'
isPrg (App pe pe') = isPrg pe && isPrg pe'
isPrg (If c e1 e2) = isPrg c && isPrg e1 && isPrg e2
isPrg (Case e patterns) = isPrg e && (and $ map (\(p,e) -> isPrg p && isPrg e) patterns)
isPrg (Paren pe) = isPrg pe
isPrg _ = True







