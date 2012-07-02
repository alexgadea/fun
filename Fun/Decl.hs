
module Fun.Decl where

import qualified Equ.PreExpr as PE
import Equ.Syntax
import Equ.Rule
import Equ.Proof
import Equ.Types
import Data.Text hiding (map)



{- Decl representa declaraciones en Fun. Una especificacion sera una pre-expresión
   en funcion de algunas teorias.
   Una funcion estará definida por una expresión que es ejecutable. No todas las expresiones
   cumplen esta propiedad, por lo que damos un predicado al respecto. -}
data Decl = Spec Func [Variable] PE.PreExpr
          | Prop Text PE.PreExpr
          | Thm Text Relation PE.PreExpr PE.PreExpr Proof
          | Fun Func [Variable] PE.PreExpr -- como hacemos con el derived from...?
          | Val Variable PE.PreExpr
          | NewType Type [Constant] [(Operator,[Variable],PE.PreExpr)] -- Para implementar a futuro.
        deriving Show

isPrg :: PE.PreExpr -> Bool
isPrg (PE.Quant _ _ _ _) = False
isPrg (PE.PrExHole _) = False
isPrg (PE.UnOp op pe) = isPrg pe
isPrg (PE.BinOp op pe pe') = isPrg pe && isPrg pe'
isPrg (PE.App pe pe') = isPrg pe && isPrg pe'
isPrg (PE.If c e1 e2) = isPrg c && isPrg e1 && isPrg e2
isPrg (PE.Case e patterns) = isPrg e && (and $ map (\(p,e) -> isPrg p && isPrg e) patterns)
isPrg (PE.Paren pe) = isPrg pe
isPrg _ = True


getFuncDecl :: Decl -> Maybe Func
getFuncDecl (Spec f _ _) = Just f
getFuncDecl (Fun f _ _) = Just f
getFuncDecl _ = Nothing

getExprDecl :: Decl -> Maybe PE.PreExpr
getExprDecl (Spec _ _ p) = Just p
getExprDecl (Prop _ p) = Just p
getExprDecl (Fun _ _ p) = Just p
getExprDecl (Val _ p) = Just p


