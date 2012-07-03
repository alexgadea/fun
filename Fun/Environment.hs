module Fun.Environment where

import Fun.Module

-- | Environment es el conjunto de módulos que se tienen cargados en un momento dado
--   en Fun. Cada vez que se hace un import desde un módulo, debe referirse a un
--   módulo que se encuentre en el environment.
type Environment = [Module]

-- | Chequea que un modulo sea correcto:
{-   No hay dobles definiciones de funciones.
     Los teoremas estén definidos.
     
checkModule :: Module -> Environment -> Either ModuleError ()
checkModule m env = 

   -}
















