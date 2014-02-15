-- | Define la noción de derivación de una función en base a una especificación
-- y una prueba, es decir, una derivación propia de la función.
module Fun.Derivation (
      Derivation (..)
    , module Fun.Derivation.Error
    , createDerivations
    , checkDerivation
    )
    where

import Fun.Decl
import Fun.Decl.Error
import Fun.Declarations
import Fun.Derivation.Derivation
import Fun.Derivation.Error

import Equ.Proof
import Equ.Expr
import Equ.Rule (getRelationFromType,Relation)
import Equ.TypeChecker (getType,typeCheckPreExpr)
import Equ.Theories

import Equ.Syntax
import qualified Equ.PreExpr as PE

import qualified Data.Text as T hiding (map,foldl)
import Data.List as L (map, find)
import Data.Either 
import qualified Data.Map as M
import qualified Data.Set as Set

import Data.Maybe (fromJust)
import Data.Monoid

import Control.Arrow ((***))
import Control.Lens

-- | A partir de las declaraciones, crea los objetos "Derivation" juntando la informacion
--   de cada especificación con la correspondiente derivación y def de función en caso que
--   ocurra. Por ahora no se puede hacer más de una derivación de una misma especificación.
--   Además, la especificación de una derivación debe estar EN EL MISMO módulo que la derivación.
createDerivations:: Declarations -> [EDeriv]
createDerivations decls = foldl (createDeriv spcs fncs) [] drvs
    where drvs = decls ^. derivs 
          spcs = bare specs decls
          fncs = bare functions decls


createDeriv :: [SpecDecl] -> [FunDecl] -> [EDeriv] -> (DeclPos,DerivDecl) -> [EDeriv]
createDeriv pSpecs pFuncs prevDerivs (derPos,der) = der':prevDerivs
    where  der' = alreadyDefined der (rights prevDerivs) >>
                  maybe (Left ([NotSpecification],der)) newDer 
                        (L.find (sameDecl der) pSpecs)
           newDer sp = Right $ Derivation der derPos sp 
                              $ L.find (sameDecl der) pFuncs

alreadyDefined :: DerivDecl -> [Derivation] -> EDeriv' ()
alreadyDefined derDecl = mconcat . map (checkRedef derDecl . deriv)

checkRedef :: (Decl d) => d -> DerivDecl -> EDeriv' ()
checkRedef d d' = if sameDecl d d'
                  then Left ([RedefinedDerivation $ getNameDecl d'],d')
                  else mempty
            

-- | Funcion que dada una derivacion dice si es válida o no. Esto es solo para las derivaciones
--   por recursión. Si luego se implementa otro tipo de derivación, entonces debería diferenciarse
checkDerivation :: Declarations -> Declarations -> [ThmDecl] -> 
                   EDeriv -> EDeriv' (DeclPos,FunDecl)
checkDerivation _ _ _ (Left e) = Left e
checkDerivation decls imDecls thms (Right der) = 
            let (declS,mDeclF,declD) = (spec der,prog der,deriv der) in
                -- primero chequeamos que la variable sobre la que se hace
                -- la derivación por recursión es la misma que está definida en
                -- la especificación.
                return (getVarsDecl declD) >>= \(Just [v]) ->
                return (tRepr v) >>= \vname ->
                return (L.map tRepr $ fromJust $ getVarsDecl declS) >>= \spVars ->
                whenDer (vname `elem` spVars) ([InvalidVariable  v],declD) >>
                -- Remplazamos la variable por la de la especificación, ya que ésta está
                -- tipada.
                getVarInSpec v declS declD >>= \vspec' -> 
                typeVariable vspec' declS declD >>= \vspec ->
                return declD >>= \(Deriv f _ pfsnt) ->
                typeCases pfsnt declD >>= \pfs ->
                return (Deriv f vspec pfs) >>= \declD' ->
                -- Ahora construimos una prueba inductiva con los datos de la derivación.
                -- Se asume que la declaración está bien tipada
                return (getExprDecl declS) >>= \(Just expr) ->
                return (getType expr) >>= \(Just texpr) ->
                return (getRelationFromType texpr) >>= \rel -> 
                firstExpr declS declD' >>= \fexpr ->
                caseExprFromDerivation declS vspec declD' >>= \caseExpr ->
                -- agregar como hipotesis la especificacion
                return (createHypothesis (T.concat [T.pack "spec ",tRepr f]) (makeExpr rel fexpr expr)
                                 (GenConditions [])) >>= \hypSpec ->
                addHypInSubProofs hypSpec pfs >>= \pfs' ->
                return (addHypothesis' hypSpec M.empty) >>= \ctx ->
                
                return (Ind ctx rel (PE.toFocus fexpr) (PE.toFocus caseExpr) 
                                    (PE.toFocus $ PE.Var vspec) pfs') >>= 
                \proof' -> 
                -- Agregamos todas las declaraciones como hipotesis
                return (addDeclHypothesis decls thms imDecls proof') >>= \proof ->

                return (validateProof proof) >>= \pmProof ->
                case pmProof of
                     Left err -> Left ([ProofNotValid err],declD')
                     Right _ -> createFunDecl declS vspec declD' (derivPos der) >>= \(pos,derivedFun) ->
                                case mDeclF of
                                     Nothing -> return (pos,derivedFun)
                                     Just declF -> if isEq declF derivedFun
                                                      then return (pos,derivedFun)
                                                      else Left ([DerivedFunctionDeclaredNotEqual f],declD')
                                
    where makeExpr :: Relation -> PE.PreExpr -> PE.PreExpr -> Expr
          makeExpr r e e' = Expr $ PE.BinOp (relToOp r) e e'
          addHypInSubProofs :: Hypothesis -> [(PE.Focus,Proof)] -> EDeriv' [(PE.Focus,Proof)]
          addHypInSubProofs hyp pfs = return $ L.map (\(f,p) -> 
                                        let Right ctx = getCtx p in
                                            let ctx' = addHypothesis' hyp ctx in
                                                let Right p' = setCtx ctx' p in
                                                    (f,p')) pfs
          isEq (Fun v vs expr _) (Fun v' vs' expr' _) = v==v' && vs==vs' && expr==expr'
                                
getVarInSpec :: Variable -> SpecDecl -> DerivDecl -> EDeriv' Variable
getVarInSpec v decl derDecl =
    let Just varsDecl = getVarsDecl decl in
        getVarInSpec' v varsDecl
        
    where getVarInSpec' v' [] = Left ([InvalidVariable v'],derDecl)
          getVarInSpec' v' (w:ws) = if tRepr v' == tRepr w
                                    then return w
                                    else getVarInSpec' v' ws


firstExpr :: SpecDecl -> DerivDecl -> EDeriv' PE.PreExpr
firstExpr spDecl _ = 
    return (getFuncDecl spDecl) >>= \(Just f) ->
    return (getVarsDecl spDecl) >>= \(Just vs) ->
    return (exprApplyFun f vs)
    
    where exprApplyFun :: Variable -> [Variable] -> PE.PreExpr
          exprApplyFun f = foldl (\e -> PE.App e . PE.Var) (PE.Var f)

createFunDecl :: SpecDecl -> Variable -> DerivDecl -> DeclPos -> EDeriv' (DeclPos,FunDecl)
createFunDecl specDecl v derDecl derPos = 
    let Just vars = getVarsDecl specDecl in
        let Just f = getFuncDecl specDecl in
            caseExprFromDerivation specDecl v derDecl >>= \exprFun ->
            return $ (derPos,Fun f vars exprFun Nothing)

caseExprFromDerivation :: SpecDecl -> Variable -> DerivDecl -> EDeriv' PE.PreExpr
caseExprFromDerivation _ v derDecl = do
    let pattern = PE.Var v
    let Just pfs = getFocusProof derDecl
    let cases = L.map (PE.toExpr *** PE.toExpr . finalExpr) pfs
    return $ PE.Case pattern cases
    
    where finalExpr = fromRight . getEnd 
          fromRight = either (error "fromRight Left") id 
    
-- | CUANDO EL TYPE CHECKER ESTE TERMINADO NO HARIA FALTA LLAMAR A ESTAS FUNCIONES
--   YA QUE LOS PARAMETROS DE UNA DECLARACION SIEMPRE TENDRAN EL TIPO
typeVariable :: Variable -> SpecDecl -> DerivDecl -> EDeriv' Variable
typeVariable v declS declD =
    return (getExprDecl declS) >>= \(Just expr) ->
    either (const $ Left ([InvalidVariable  v],declD)) return (typeCheckPreExpr expr)
    >>= \typedExpr -> maybe (Left ([InvalidVariable  v],declD)) 
                      return
                      (L.find (==v) (Set.toList (PE.freeVars typedExpr)))               
                      
typeCases :: [(PE.Focus,Proof)] -> DerivDecl -> EDeriv' [(PE.Focus,Proof)]
typeCases cs declD = let tc_cs = map (\(f,p) -> (typeCheckPreExpr $ PE.toExpr f,p)) cs in
                     if lefts (map fst tc_cs) /= []
                      then Left ([TypesError],declD)
                      else return (map (\(Right e,p) -> (PE.toFocus e,p)) tc_cs)         
                      
