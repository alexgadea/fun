
module Fun.Patterns where

import Fun.IndType
import Fun.FunTheories.Theories


-- | Funcion que asocia un tipo comun de Equ con un Tipo Inductivo de Fun
getIndType :: Type -> Maybe IndType
getIndType (TyAtom ATyNat) = natural
getIndType (TyAtom ATyBool) = bool
getIndType (TyList t) = list
                      
inductiveTypes = [natural, bool, list]
                      
                      
-- | Funcion para decidir si una expresion es pattern.
-- | No chequea tipos.
isPattern :: PreExpr -> Bool
isPattern (Var _) = True
isPattern (Con c) = elem c (map baseConstructor inductiveTypes)
isPattern (UnOp op _) t = elem op (map indConstructor inductiveTypes)
isPattern (BinOp op _ _) = elem op (map indConstructor inductiveTypes)
isPattern _ = False