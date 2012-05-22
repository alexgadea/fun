module IntTypes where

import Equ.Types
import Equ.Syntax

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
                               
    where isBaseConstructor :: Constant -> Type -> Bool
          isBaseConstructor c t = t == conTy c
          
          isIndConstructor :: Operator -> Type -> Bool
          isIndConstructor op t = case opTy op of
                                         t1 :-> t2 -> t == t2
                                         otherwise -> False