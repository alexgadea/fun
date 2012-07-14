module Fun.Derivation.Monad where

import Fun.Derivation.Derivation
import Fun.Derivation.Error
import Fun.Decl

import Equ.Syntax
import qualified Equ.PreExpr as PE


type DM a = Either (ErrInDeriv Derivation) a

-- whenDM :: (a -> Bool) -> [ErrInDeriv DerivationError] -> a -> DM a
-- whenDM p e a | p a       = return a
--              | otherwise = Left e
--              
-- whenDM' :: Bool -> [ErrInDeriv DerivationError] -> DM ()
-- whenDM' b e | b         = return ()
--             | otherwise = Left e

-- getEspecFun :: Derivation -> DM Func
-- getEspecFun =
--     maybe (Left InvalidSpec) return . getFuncDecl . espec
--     
-- getPrgFun :: Derivation -> DM Func
-- getPrgFun =
--     maybe (Left InvalidPrg) return . getFuncDecl . prog
--     
-- getEspecExpr :: Derivation -> DM PE.PreExpr
-- getEspecExpr =
--     maybe (Left InvalidSpec) return . getExprDecl . espec
--     
-- getPrgExpr :: Derivation -> DM PE.PreExpr
-- getPrgExpr =
--     maybe (Left InvalidPrg) return . getExprDecl . prog

