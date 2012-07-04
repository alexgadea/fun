
module Fun.Decl where

import qualified Equ.PreExpr as PE
import Equ.Syntax
import Equ.Rule
import Equ.Proof
import Equ.Types
import Equ.Expr
import Data.Text hiding (map)


-- | Declaraciones en Fun

data SpecDecl = Spec Func [Variable] PE.PreExpr
    deriving (Eq,Show)

data PropDecl = Prop Text PE.PreExpr
    deriving (Eq,Show)

data ThmDecl = Thm Theorem
    deriving (Eq,Show)

data FunDecl = Fun Func [Variable] PE.PreExpr (Maybe Text) -- Puede tener la derivación o no.
    deriving (Eq,Show)

data ValDecl = Val Variable PE.PreExpr
    deriving (Eq,Show)

data TypeDecl = NewType Type [Constant] [(Operator,[Variable],PE.PreExpr)] -- Para implementar a futuro.
    deriving (Eq,Show)


class Decl a where
    getFuncDecl :: a -> Maybe Func
    getExprDecl :: a -> Maybe PE.PreExpr

instance Decl SpecDecl where
    getFuncDecl (Spec f _ _) = Just f
    getExprDecl (Spec _ _ e) = Just e
    
instance Decl PropDecl where
    getFuncDecl _ = Nothing
    getExprDecl (Prop _ e) = Just e
    
instance Decl ThmDecl where
    getFuncDecl _ = Nothing
    getExprDecl (Thm t) = let (Expr p) = thExpr t in
                              Just p
    
instance Decl FunDecl where
    getFuncDecl (Fun f _ _ _) = Just f
    getExprDecl (Fun _ _ p _) = Just p
    
instance Decl ValDecl where
    getFuncDecl _ = Nothing
    getExprDecl (Val _ p) = Just p
    
instance Decl TypeDecl where
    getFuncDecl _ = Nothing
    getExprDecl _ = Nothing

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



