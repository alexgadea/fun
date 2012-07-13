
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
    deriving Show

instance Eq SpecDecl where
    (Spec f _ _) == (Spec f' _ _) = f == f'

data PropDecl = Prop Text PE.PreExpr
    deriving Show

instance Eq PropDecl where
    (Prop t _) == (Prop t' _) = t == t'

data ThmDecl = Thm Theorem
    deriving Show

instance Eq ThmDecl where
    thm == thm' = getThmName thm == getThmName thm'

data FunDecl = Fun Func [Variable] PE.PreExpr (Maybe Text) -- Puede tener la derivación o no.
    deriving Show

instance Eq FunDecl where
    (Fun f _ _ _) == (Fun f' _ _ _) = f == f'

data ValDecl = Val Variable PE.PreExpr
    deriving Show
    
instance Eq ValDecl where
    (Val v _) == (Val v' _) = v == v'


data OpDecl = OpDecl Operator [Variable] PE.PreExpr
    deriving Show

instance Eq OpDecl where
    (OpDecl op _ _) == (OpDecl op' _ _) = op == op'


data TypeDecl = NewType Type [Constant] [(Operator,[Variable],PE.PreExpr)] -- Para implementar a futuro.
    deriving (Eq,Show)

getThmName :: ThmDecl -> Text
getThmName (Thm t) = truthName t

getFunDerivingFrom :: FunDecl -> Maybe Text
getFunDerivingFrom (Fun _ _ _ mt) = mt

class Decl a where
    getFuncDecl :: a -> Maybe Func
    getExprDecl :: a -> Maybe PE.PreExpr
    getVarsDecl :: a -> Maybe [Variable]

instance Decl SpecDecl where
    getFuncDecl (Spec f _ _) = Just f
    getExprDecl (Spec _ _ e) = Just e
    getVarsDecl (Spec _ vs _) = Just vs
    
instance Decl PropDecl where
    getFuncDecl _ = Nothing
    getExprDecl (Prop _ e) = Just e
    getVarsDecl _ = Nothing
    
instance Decl ThmDecl where
    getFuncDecl _ = Nothing
    getExprDecl (Thm t) = let (Expr p) = thExpr t in Just p
    getVarsDecl _ = Nothing
    
instance Decl FunDecl where
    getFuncDecl (Fun f _ _ _) = Just f
    getExprDecl (Fun _ _ p _) = Just p
    getVarsDecl (Fun _ vs _ _) = Just vs
    
instance Decl ValDecl where
    getFuncDecl _ = Nothing
    getExprDecl (Val _ p) = Just p
    getVarsDecl _ = Nothing
    
instance Decl TypeDecl where
    getFuncDecl _ = Nothing
    getExprDecl _ = Nothing
    getVarsDecl _ = Nothing

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
