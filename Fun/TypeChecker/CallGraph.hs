{-# Language TemplateHaskell #-}
module Fun.TypeChecker.CallGraph (mutualBlocks)
    where

import Equ.PreExpr

import Data.Graph.Inductive

import Data.List
import Control.Monad.Trans.State
import Control.Lens
-- import Lens.Family

import Control.Applicative 

-- | Grafo con variables en los nodos y aristas sin etiquetas.
type CallGraph = Gr Variable ()

data GrConstr = GrConstr { _idx :: Int
                         , _nds :: [LNode Variable]
                         }
$(makeLenses ''GrConstr)

initGrConstr :: GrConstr
initGrConstr = GrConstr 0 []

mkCallGraph :: [(Variable,[Variable],PreExpr)] -> CallGraph
mkCallGraph fs = let (es,st) = runState (mapM go fs) initGrConstr
                 in mkGraph (st ^. nds) (concat es)
    where go (f,args,body) = addNode f >> addEdges f args body


addNode :: Variable -> State GrConstr (LNode Variable)
addNode v = lookupNode v >>= maybe (newNode v) (\n -> return (n,v))

newNode :: Variable -> State GrConstr (LNode Variable)
newNode v = use idx >>= \n -> 
            idx %= (+1) >> 
            nds %= ((n,v):) >>
            return (n,v)

lookupNode :: Variable -> State GrConstr (Maybe Node)
lookupNode v = maybe Nothing (Just . fst) . find ((v ==) . snd) <$> use nds

addEdge :: Variable -> Variable -> State GrConstr UEdge
addEdge f g = addNode f >>= \(nf,_) ->
              addNode g >>= \(ng,_) ->
              return (nf,ng,())

addEdges :: Variable -> [Variable] -> PreExpr -> State GrConstr [UEdge]
addEdges f args body = mapM (addEdge f) $ getCalledVars body \\ args

connectedCalls :: CallGraph -> [[Variable]]
connectedCalls gr = map (map getN) $ scc gr
    where getN n = maybe (error "IMPOSSIBLE") id $ lookup n (labNodes gr)

mutualBlocks' :: [(Variable,[Variable],PreExpr)] -> [[Variable]]
mutualBlocks' = connectedCalls . mkCallGraph

mutualBlocks :: [(Variable,[Variable],PreExpr)] -> [[Variable]]
mutualBlocks fs = [[g | g <- map fst' fs, f <- fs' , g == f] | fs' <- fss]
    where fss = mutualBlocks' fs
          fst' (a,_,_) = a
