-- Representación de los modulos cargados en un environment en relación con sus
-- imports.
module Fun.Module.Graph where

import Fun.Module

import Data.Graph.Inductive
import Data.Graph.Inductive.Graph
import Data.Graph.Inductive.Query.DFS
import Data.Maybe (fromJust)
import Data.Tuple (swap)
import Data.List (zip3,replicate,nub)

import Control.Lens

type ImModuleGraph = Gr ModName ()

-- | Grafo vacio de imports
emptyImMG :: ImModuleGraph 
emptyImMG = empty 

-- | Dado un módulo y un grafo, agrega los imports de este módulo.
insModuleImports :: Module -> ImModuleGraph -> ImModuleGraph 
insModuleImports m imMGraph = 
        (\g -> insEdges (fromJust $ mImEdges g) g) $ insNodes mImNodes imMGraph
    where
        mImNames' :: [ModName]
        mImNames' = filter (`notElem` map snd (labNodes imMGraph)) (nub $ m ^. modName : mImNames)
        mImNames :: [ModName]
        mImNames = map (\(Import m) -> m) $ m ^. imports
        mImNodes :: [LNode ModName]
        mImNodes = mkNodes_ (fromGraph imMGraph) mImNames'
        numImports :: Int
        numImports = length $  m ^. imports
        mImEdges :: ImModuleGraph -> Maybe [LEdge ()]
        mImEdges g = mkEdges (fromGraph g) $ 
                                zip3 (replicate numImports $ m ^. modName )
                                     mImNames
                                     (replicate numImports ())

-- | Retorna una lista con los nombre de módulos que alcanza teniendo encuenta
-- cadena de imports.
reachableImports :: ModName -> ImModuleGraph -> [ModName]
reachableImports modN imG = tail $ map getName $ reachable modNNumber imG
    where
        getName :: Node -> ModName
        getName n = fromJust $ lookup n nodeMap
        nodeMap :: [LNode ModName]
        nodeMap = labNodes imG
        modNNumber :: Node
        modNNumber = fromJust $ pukool modN nodeMap
        pukool :: ModName -> [LNode ModName] -> Maybe Node
        pukool n nm = lookup n (map swap nm)

