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
import Equ.Rule (getRelationFromType)
import Equ.TypeChecker (getType)
import Equ.Theories
import Equ.Theories.FOL 
import Equ.Syntax
import qualified Equ.PreExpr as PE

import Data.Text hiding (map,foldl)
import Data.List as L (map, find)
import Data.Map as M
import Data.Either (rights)
import Data.Maybe (fromJust)

import System.IO.Unsafe (unsafePerformIO)


-- | A partir de las declaraciones, crea los objetos "Derivation" juntando la informacion
--   de cada especificación con la correspondiente derivación y def de función en caso que
--   ocurra. Por ahora no se puede hacer más de una derivación de una misma especificación.
createDerivations:: Declarations -> [EDeriv]
createDerivations decls =
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
            
        equalFunc :: Decl d => Text -> d -> Bool
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
                getVarInSpec v declS declD >>= \vspec -> return declD >>= \(Deriv f _ pfs) ->
                return (Deriv f vspec pfs) >>= \declD' ->
                -- Ahora construimos una prueba inductiva con los datos de la derivación.
                -- Se asume que la declaración está bien tipada
                return (getExprDecl declS) >>= \(Just expr) -> 
                unsafePerformIO (putStrLn ("Expresion ::::: "++show expr) >>
                                 return (return ())) >>
                return (getType expr) >>= \mt -> 
                unsafePerformIO (putStrLn 
                                ("Expresion es = "++show expr ++
                                ", tipo de la expresion= "++show mt) >>
                                return (return ())) >>
                return (fromJust mt) >>= \texpr ->
                                                    -- \(Just texpr) ->
                return (getRelationFromType texpr) >>= \rel -> 
                firstExpr declS declD' >>= \fexpr ->
                return (Ind M.empty rel (PE.toFocus $ PE.Var vspec) fexpr (PE.toFocus expr) pfs) >>= \proof ->
                return (validateProof proof) >>= \pmProof ->
                case pmProof of
                     Left err -> Left ([ProofNotValid err],declD')
                     Right _ -> createFunDecl declS vspec declD' (derivPos der) >>=
                                return
                                
getVarInSpec :: Variable -> SpecDecl -> DerivDecl -> EDeriv' Variable
getVarInSpec v decl derDecl =
    let Just varsDecl = getVarsDecl decl in
        getVarInSpec' v varsDecl
        
    where getVarInSpec' v [] = Left ([InvalidVariable v],derDecl)
          getVarInSpec' v (w:ws) = if tRepr v == tRepr w
                                      then return w
                                      else getVarInSpec' v ws


firstExpr :: SpecDecl -> DerivDecl -> EDeriv' PE.Focus
firstExpr spDecl derDecl =
    return (getFuncDecl spDecl) >>= \(Just f) ->
    return (getVarsDecl spDecl) >>= \(Just vs) ->
    return (PE.toFocus $ exprApplyFun f vs)
    
    where exprApplyFun :: Variable -> [Variable] -> PE.PreExpr
          exprApplyFun f vs =
              foldl (\e v -> PE.App e (PE.Var v)) (PE.Var f) vs

createFunDecl :: SpecDecl -> Variable -> DerivDecl -> DeclPos -> EDeriv' (DeclPos,FunDecl)
createFunDecl specDecl v derDecl derPos = do
    let Just fun = getFuncDecl specDecl
    let Just vars = getVarsDecl specDecl
    let pattern = PE.Var v
    let Just pfs = getFocusProof derDecl
    let cases = L.map (\(f,p) -> (PE.toExpr f,PE.toExpr $ finalExpr p)) pfs
    let exprFun = PE.Case pattern cases
    return $ (derPos,Fun v vars exprFun Nothing)
    
    where finalExpr p = fromRight $ getEnd p
          fromRight e = case e of
                             Left _ -> error "fromRight Left"
                             Right e' -> e'
    
                                      
                                      