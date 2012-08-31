
module Fun.Decl where

import qualified Equ.PreExpr as PE
import Equ.Syntax
import Equ.Rule
import Equ.Proof
import Equ.Types
import Equ.Expr
import Equ.TypeChecker (getType)
import Equ.Theories (createHypothesis,makeExprFromRelation)
import Data.Text hiding (map,all)
import Fun.Decl.Error
import Data.Text (pack,unpack,Text)

-- | Declaraciones en Fun
data SpecDecl = Spec Variable [Variable] PE.PreExpr
    deriving Show

instance Eq SpecDecl where
    (Spec f _ _) == (Spec f' _ _) = f == f'

data PropDecl = Prop Text PE.PreExpr
    deriving Show

instance Eq PropDecl where
    (Prop t _) == (Prop t' _) = t == t'

data ThmDecl = Thm Theorem

instance Show ThmDecl where
    show (Thm t) = show $ thExpr t

instance Eq ThmDecl where
    thm == thm' = getNameDecl thm == getNameDecl thm'

data FunDecl = Fun Variable [Variable] PE.PreExpr (Maybe Text) -- Puede tener la verificación o no.
    deriving Show

-- POR QUE ESTA INSTANCIA ESTA DEFINIDA ASI??????
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

data DerivDecl = Deriv Variable Variable [(PE.Focus,Proof)]

instance Show DerivDecl where
    show (Deriv v v' fps) = "Deriv "
                          ++ show v ++ " " ++ show v' ++ " " 
                          ++ show (map fst fps)

instance Eq DerivDecl where
    (Deriv v _ _) == (Deriv v' _ _) = v == v'
    
data TypeDecl = NewType Type [Constant] [(Operator,[Variable],PE.PreExpr)] -- Para implementar a futuro.
    deriving (Eq,Show)

getFunDerivingFrom :: FunDecl -> Maybe Text
getFunDerivingFrom (Fun _ _ _ mt) = mt

class Decl a where
    getNameDecl   :: a -> Text
    getFuncDecl   :: a -> Maybe Variable
    getExprDecl   :: a -> Maybe PE.PreExpr
    getVarsDecl   :: a -> Maybe [Variable]
    getFocusProof :: a -> Maybe [(PE.Focus,Proof)]
    createHypDecl :: a -> Maybe Hypothesis

instance Decl SpecDecl where
    getNameDecl (Spec f _ _) = tRepr f
    getFuncDecl (Spec f _ _) = Just f
    getExprDecl (Spec _ _ e) = Just e
    getVarsDecl (Spec _ vs _) = Just vs
    getFocusProof _ = Nothing
    createHypDecl (Spec f vs e) = 
        getType e >>= \te -> (\rel ->
        return $ createHypothesis (pack $ "spec "++show f)
                                  (makeExprFromRelation rel (PE.exprApply f vs) e)
                                  (GenConditions [])) (getRelationFromType te)
instance Decl PropDecl where
    getNameDecl (Prop t _) = t
    getFuncDecl _ = Nothing
    getExprDecl (Prop _ e) = Just e
    getVarsDecl _ = Nothing
    getFocusProof _ = Nothing
    createHypDecl (Prop t e) =
        Just $ createHypothesis (pack $ "prop "++ unpack t)
                                (Expr e) (GenConditions [])
    
instance Decl ThmDecl where
    getNameDecl (Thm t) =  truthName t
    getFuncDecl _ = Nothing
    getExprDecl (Thm t) = let (Expr p) = thExpr t in Just p
    getVarsDecl _ = Nothing
    getFocusProof _ = Nothing
    createHypDecl (Thm t) = 
        Just $ createHypothesis (truthName t) (thExpr t) (GenConditions [])
    
instance Decl FunDecl where
    getNameDecl (Fun f _ _ _) =  tRepr f
    getFuncDecl (Fun f _ _ _) = Just f
    getExprDecl (Fun _ _ p _) = Just p
    getVarsDecl (Fun _ vs _ _) = Just vs
    getFocusProof _ = Nothing
    createHypDecl (Fun f vs e _) = 
        getType e >>= \te -> (\rel ->
        return $ createHypothesis (pack $ "fun "++show f)
                                  (makeExprFromRelation rel (PE.exprApply f vs) e)
                                  (GenConditions [])) (getRelationFromType te)
    
instance Decl ValDecl where
    getNameDecl (Val v _) =  tRepr v
    getFuncDecl _ = Nothing
    getExprDecl (Val _ p) = Just p
    getVarsDecl _ = Nothing
    getFocusProof _ = Nothing
    createHypDecl (Val v e) =
        getType e >>= \te -> (\rel ->
        return $ createHypothesis (pack $ "val "++ show v)
                                  (makeExprFromRelation rel (PE.Var v) e)
                                  (GenConditions [])) (getRelationFromType te)

instance Decl DerivDecl where
    getNameDecl   (Deriv v _ _) = tRepr v
    getFuncDecl   (Deriv v _ _) = Just v
    getVarsDecl   (Deriv _ v _) = Just [v]
    getFocusProof (Deriv _ _ fps) = Just fps
    getExprDecl _ = Nothing
    createHypDecl (Deriv _ _ _) = Nothing

instance Decl TypeDecl where
    getNameDecl _ =  pack ""
    getFuncDecl _ = Nothing
    getExprDecl _ = Nothing
    getVarsDecl _ = Nothing
    getFocusProof _ = Nothing
    createHypDecl _ = Nothing

isPrg :: PE.PreExpr -> Bool
isPrg (PE.Quant _ _ _ _) = False
isPrg (PE.PrExHole _) = False
isPrg (PE.UnOp op pe) = isPrg pe
isPrg (PE.BinOp op pe pe') = isPrg pe && isPrg pe'
isPrg (PE.App pe pe') = isPrg pe && isPrg pe'
isPrg (PE.If c e1 e2) = isPrg c && isPrg e1 && isPrg e2
isPrg (PE.Case e patterns) = isPrg e && all (\(p,e) -> isPrg p && isPrg e) patterns
isPrg (PE.Paren pe) = isPrg pe
isPrg _ = True
