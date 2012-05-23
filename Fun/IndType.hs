module Fun.IndType where

import Equ.Types
import Equ.Syntax
import Equ.TypeChecker(unifyTest)

import Data.Text hiding (map)


-- | Un tipo inductivo permite realizar Pattern Matching. Está relacionado con una teoria.
data IndType = IndType {
            name :: Text
          , ty :: Type
          , baseConstructors :: [Constant]
          , indConstructors :: [Operator]
}


-- | Un tipo inductivo valido debe ser construido con la siguiente funcion.
-- | Si es el tipo que se quiere construir, t, es válido devuelve Just t. Otro caso Nothing.
createIndType :: Text -> Type -> [Constant] -> [Operator] -> Maybe IndType
createIndType name t bcons icons = if (and $ map (flip isBaseConstructor t) bcons) &&
                                      (and $ map (flip isIndConstructor t) icons)
                                       then Just $ IndType {
                                            name = name
                                          , ty = t
                                          , baseConstructors = bcons
                                          , indConstructors = icons
                                       }
                                      else Nothing
                                       
                                         
isValidIndType :: IndType -> Bool
isValidIndType it = 
    (and $ map (flip isBaseConstructor (ty it)) bcons) &&
    (and $ map (flip isIndConstructor (ty it)) icons)
    
    where bcons = baseConstructors it
          icons = indConstructors it
          
          
          
isBaseConstructor :: Constant -> Type -> Bool
isBaseConstructor c t = unifyTest t (conTy c)
          
isIndConstructor :: Operator -> Type -> Bool
isIndConstructor op t = case opTy op of
                            t1 :-> t2 -> unifyTest t t2   -- En vez de igualdad no deberia ser que sean unificables??
                            otherwise -> False