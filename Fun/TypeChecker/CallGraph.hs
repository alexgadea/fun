{-# Language TemplateHaskell #-}
module Fun.TypeChecker.CallGraph (mutualBlocks)
    where

import Fun.Decl

import Equ.PreExpr

import Data.Graph.Inductive
import Data.Graph.Inductive.Query.DFS

import Data.List
import Control.Monad.Trans.State
import Lens.Family.TH
import Lens.Family

import Control.Applicative 

-- | Grafo con variables en los nodos y aristas sin etiquetas.
type CallGraph = Gr Variable ()

data GrConstr = GrConstr { _idx :: Int
                         , _nds :: [LNode Variable]
                         }
$(mkLenses ''GrConstr)


initGrConstr = GrConstr 0 []

mkCallGraph :: [FunDecl] -> CallGraph
mkCallGraph fs = let (edges,st) = runState (mapM go fs) initGrConstr
                 in mkGraph (st ^. nds) (concat edges)
    where go (Fun f args body _) = addNode f >> addEdges f args body


addNode :: Variable -> State GrConstr (LNode Variable)
addNode v = lookupNode v >>= maybe (newNode v) (\n -> return (n,v))

newNode :: Variable -> State GrConstr (LNode Variable)
newNode v = gets (^. idx) >>= \n ->
            modify (idx %~ (+1)) >> 
            modify (nds %~ ((n,v):)) >>
            return (n,v)

lookupNode :: Variable -> State GrConstr (Maybe Node)
lookupNode v = maybe Nothing (Just . fst) . find ((v ==) . snd) <$> gets (^. nds)

addEdge :: Variable -> Variable -> State GrConstr UEdge
addEdge f g = addNode f >>= \(nf,_) ->
              addNode g >>= \(ng,_) ->
              return (nf,ng,())

addEdges :: Variable -> [Variable] -> PreExpr -> State GrConstr [UEdge]
addEdges f args body = mapM (addEdge f) $ getCalledVars body \\ args

connectedCalls :: CallGraph -> [[Variable]]
connectedCalls gr = map (map getNode) $ scc gr
    where getNode n = maybe (error "IMPOSSIBLE") id $ lookup n (labNodes gr)

mutualBlocks' :: [FunDecl] -> [[Variable]]
mutualBlocks' = connectedCalls . mkCallGraph

mutualBlocks :: [FunDecl] -> [[FunDecl]]
mutualBlocks fs = [[g | g <- fs, f <- fs' ,eqFun g f] | fs' <- fss]
    where fss = mutualBlocks' fs
          eqFun (Fun f _ _ _) g = f == g