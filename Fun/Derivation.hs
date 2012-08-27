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

import Equ.Expr
import Equ.Proof
import Equ.Rule (getRelationFromType,Relation)
import Equ.TypeChecker (getType,typeCheckPreExpr)
import Equ.Theories
import Equ.Theories.FOL 
import Equ.Syntax
import qualified Equ.PreExpr as PE

import qualified Data.Text as T hiding (map,foldl)
import Data.List as L (map, find)
import qualified Data.Map as M
import qualified Data.Set as Set
import Data.Either (rights,lefts)
import Data.Maybe (fromJust)

import System.IO.Unsafe (unsafePerformIO)


-- | A partir de las declaraciones, crea los objetos "Derivation" juntando la informacion
--   de cada especificación con la correspondiente derivación y def de función en caso que
--   ocurra. Por ahora no se puede hacer más de una derivación de una misma especificación.
createDerivations:: Declarations -> Maybe Declarations -> [EDeriv]
createDerivations decls dswi =
    -- Obtenemos las declaraciones parseadas
    let pDerivs = derivs decls in
        let pSpecs = L.map snd $ specs decls in
            let pFuncs = L.map snd $ functions decls in
                foldl (createDeriv pSpecs pFuncs) [] pDerivs
    
    where 
        createDeriv :: [SpecDecl] -> [FunDecl] -> [EDeriv] -> (DeclPos,DerivDecl) -> [EDeriv]
        createDeriv pSpecs pFuncs prevDerivs (derPos,deriv) = 
            let funcname = getNameDecl deriv in
                (checkRedefinition prevDerivs deriv >>
                maybe (Left ([NotSpecification],deriv))
                    (\spec -> 
                    maybe (Right $ Derivation deriv derPos spec Nothing)
                            (\func -> Right $ Derivation deriv derPos spec (Just func))
                            (L.find (equalFunc funcname) pFuncs)
                    )
                    (L.find (equalFunc funcname) pSpecs)
                ):prevDerivs
            
        equalFunc :: Decl d => T.Text -> d -> Bool
        equalFunc name d = getNameDecl d == name
        
        checkRedefinition :: [EDeriv] -> DerivDecl -> EDeriv' ()
        checkRedefinition pderivs derDecl =
            foldl (\e d -> e >>
                       case d of
                        Left _ -> return ()
                        Right d' -> 
                                if getNameDecl (deriv d') == getNameDecl derDecl
                                    -- Ya habia una derivacion con el mismo nombre
                                    then Left ([RedefinedDerivation $ getNameDecl derDecl],derDecl)
                                    else return ())
                   (return ()) pderivs
            

-- | Funcion que dada una derivacion dice si es válida o no. Esto es solo para las derivaciones
--   por recursión. Si luego se implementa otro tipo de derivación, entonces debería diferenciarse
checkDerivation :: EDeriv -> EDeriv' (DeclPos,FunDecl)
checkDerivation d = 
    case d of
        Left e -> Left e
        Right der -> -- Hacemos el chequeo de la derivación
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
                \proof -> 
                unsafePerformIO (putStrLn ("Prueba por validar: "++show proof) >>
                                 return (return ())) >>
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
          isEq (Fun v vs expr m) (Fun v' vs' expr' m') = v==v' && vs==vs' && expr==expr'
                                
getVarInSpec :: Variable -> SpecDecl -> DerivDecl -> EDeriv' Variable
getVarInSpec v decl derDecl =
    let Just varsDecl = getVarsDecl decl in
        getVarInSpec' v varsDecl
        
    where getVarInSpec' v [] = Left ([InvalidVariable v],derDecl)
          getVarInSpec' v (w:ws) = if tRepr v == tRepr w
                                      then return w
                                      else getVarInSpec' v ws


firstExpr :: SpecDecl -> DerivDecl -> EDeriv' PE.PreExpr
firstExpr spDecl derDecl =
    return (getFuncDecl spDecl) >>= \(Just f) ->
    return (getVarsDecl spDecl) >>= \(Just vs) ->
    return (exprApplyFun f vs)
    
    where exprApplyFun :: Variable -> [Variable] -> PE.PreExpr
          exprApplyFun f vs =
              foldl (\e v -> PE.App e (PE.Var v)) (PE.Var f) vs

createFunDecl :: SpecDecl -> Variable -> DerivDecl -> DeclPos -> EDeriv' (DeclPos,FunDecl)
createFunDecl specDecl v derDecl derPos = 
    let Just vars = getVarsDecl specDecl in
        let Just f = getFuncDecl specDecl in
            caseExprFromDerivation specDecl v derDecl >>= \exprFun ->
            return $ (derPos,Fun f vars exprFun Nothing)

caseExprFromDerivation :: SpecDecl -> Variable -> DerivDecl -> EDeriv' PE.PreExpr
caseExprFromDerivation specDecl v derDecl = do
    let Just fun = getFuncDecl specDecl
    let Just vars = getVarsDecl specDecl
    let pattern = PE.Var v
    let Just pfs = getFocusProof derDecl
    let cases = L.map (\(f,p) -> (PE.toExpr f,PE.toExpr $ finalExpr p)) pfs
    return $ PE.Case pattern cases
    
    where finalExpr p = fromRight $ getEnd p 
          fromRight e = case e of
                            Left _ -> error "fromRight Left"
                            Right e' -> e'
    
-- | CUANDO EL TYPE CHECKER ESTE TERMINADO NO HARIA FALTA LLAMAR A ESTAS FUNCIONES
--   YA QUE LOS PARAMETROS DE UNA DECLARACION SIEMPRE TENDRAN EL TIPO
typeVariable :: Variable -> SpecDecl -> DerivDecl -> EDeriv' Variable
typeVariable v declS declD =
    return (getExprDecl declS) >>= \(Just expr) ->
    either (\e -> Left ([InvalidVariable  v],declD)) return (typeCheckPreExpr expr)
    >>= \typedExpr -> maybe (Left ([InvalidVariable  v],declD)) 
                      return
                      (L.find (==v) (Set.toList (PE.freeVars typedExpr)))               
                      
typeCases :: [(PE.Focus,Proof)] -> DerivDecl -> EDeriv' [(PE.Focus,Proof)]
typeCases cs declD = let tc_cs = map (\(f,p) -> (typeCheckPreExpr $ PE.toExpr f,p)) cs in
                   if lefts (map fst tc_cs) /= []
                      then Left ([TypesError],declD)
                      else return (map (\(Right e,p) -> (PE.toFocus e,p)) tc_cs)         
                      