
module Fun.Declarations where

import Equ.Syntax hiding (Func)
import Equ.Theories (createHypothesis)
import qualified Equ.PreExpr as PE (PreExpr, freeVars)
import Equ.Proof hiding (setCtx, getCtx)
import Equ.Proof.Proof
import Equ.Proof.Condition
import Equ.Types

import Fun.Theories
import Fun.Theory
import Fun.Decl
import Fun.Decl.Error
import Fun.Derivation.Error
import Fun.Verification.Error
import Equ.IndType

import qualified Data.List as L ( map,elem,delete,filter
                                , concatMap, foldl,length
                                , concat, notElem)
import qualified Data.Set as S (toList)
import qualified Data.Map as M
import Data.Text hiding (map,concatMap,unlines,reverse)
import Data.Either (lefts,partitionEithers)
import Data.Maybe (fromJust,fromMaybe,mapMaybe)

import Text.Parsec.Pos (newPos)

import Control.Monad
import Control.Arrow(second)

import System.IO.Unsafe (unsafePerformIO)

data CDoubleType = CDSpec | CDFun | CDThm | CDProp | CDVal
    deriving Eq

data InvalidDeclarations = 
        InvalidDeclarations { inSpecs     :: [ErrInDecl  SpecDecl]
                            , inFunctions :: [ErrInDecl  FunDecl]
                            , inTheorems  :: [ErrInDecl  ThmDecl]
                            , inProps     :: [ErrInDecl  PropDecl]
                            , inVals      :: [ErrInDecl  ValDecl]
                            , inDerivs    :: [ErrInDeriv DerivDecl]
                            }
    deriving Show

data Declarations = 
    Declarations { specs     :: [(DeclPos,SpecDecl)]
                 , functions :: [(DeclPos,FunDecl)]
                 , theorems  :: [(DeclPos,ThmDecl)]
                 , props     :: [(DeclPos,PropDecl)]
                 , vals      :: [(DeclPos,ValDecl)]
                 , derivs    :: [(DeclPos,DerivDecl)]
                 , indTypes  :: [(Type,IndType)] -- Si luego extendemos para declarar tipos, este campo del environment va agregando cada uno de
                                           -- los nuevos tipos declarados. Por ahora usaremos solo el valor inicial que le pasamos,
                                           -- el cual contiene los tipos basicos de Equ.
                 }

filterValidDecls :: Declarations -> InvalidDeclarations -> Declarations                 
filterValidDecls vds ivds = 
             Declarations
                (L.filter (`notIn` (inSpecs ivds)) $ specs vds)
                (L.filter (`notIn` (inFunctions ivds)) $ functions vds)
                (L.filter (`notIn` (inTheorems ivds)) $ theorems vds)
                (L.filter (`notIn` (inProps ivds)) $ props vds)
                (L.filter (`notIn` (inVals ivds)) $ vals vds)
                (L.filter (`notIn'` (inDerivs ivds)) $ derivs vds)
                []
    where
        notIn' :: (Eq d, Decl d) => (DeclPos,d) -> [ErrInDeriv d] -> Bool
        notIn' (_,d) errds = d `L.notElem` (L.map snd errds)
        notIn :: (Eq d, Decl d) => (DeclPos,d) -> [ErrInDecl d] -> Bool
        notIn (_,d) errds = d `L.notElem` (L.map eDecl errds)
                 
concatDeclarations :: Declarations -> Declarations -> Declarations
concatDeclarations d d' = Declarations 
                            (specs d ++ specs d')
                            (functions d ++ functions d')
                            (theorems d ++ theorems d')
                            (props d ++ props d')
                            (vals d ++ vals d')
                            (derivs d ++ derivs d')
                            (indTypes d ++ indTypes d')

instance Show Declarations where
    show decls = unlines [ ""
                         , "Specs: "   ++ show (specs decls)
                         , "Funs:  "   ++ show (functions decls) 
                         , "Thms:  "   ++ show (theorems decls) 
                         , "Props: "   ++ show (props decls) 
                         , "Vals:  "   ++ show (vals decls)
                         , "Derivs:  " ++ "[" ++ concatMap showDer (derivs decls) ++ "]"
                         ]
        where
            showDer :: (DeclPos,DerivDecl) -> String
            showDer (dPos, Deriv v v' fps) = 
                    "(" ++ show dPos ++ "," ++ 
                    "Deriv " ++ show v ++ " " ++
                    show v' ++ " " ++ 
                    ("[" ++ concatMap (show . fst) fps ++ "]") ++ 
                    ")"

envAddFun :: Declarations -> (DeclPos,FunDecl) -> Declarations
envAddFun env f = env {functions = f : functions env}

envAddSpec :: Declarations -> (DeclPos,SpecDecl) -> Declarations
envAddSpec env s = env {specs = s : specs env} 

envAddVal :: Declarations -> (DeclPos,ValDecl) -> Declarations
envAddVal env v = env {vals = v : vals env}

envAddTheorem :: Declarations -> (DeclPos,ThmDecl) -> Declarations
envAddTheorem env p = env {theorems = p : theorems env} 

envAddProp :: Declarations -> (DeclPos,PropDecl) -> Declarations
envAddProp env p = env {props = p : props env} 

envAddDeriv :: Declarations -> (DeclPos,DerivDecl) -> Declarations
envAddDeriv env p = env {derivs = p : derivs env} 

valsDef :: Declarations -> [Variable]
valsDef = L.map (\(_,Val v _) -> v) . vals

funcsDef :: Declarations -> [Variable]
funcsDef = L.map (\(_,Fun f _ _ _) -> f) . functions

checkSpecs :: Declarations -> Maybe Declarations -> 
              [Either (ErrInDecl SpecDecl) SpecDecl]
checkSpecs ds imds = 
        L.map (\(dPos,spec) ->
            case (checkDefVar spec dswi, checkDoubleDef CDSpec (dPos,spec) dswi) of
                ([],[]) -> Right spec
                (vErrs,dErrs) -> Left $ ErrInDecl dPos (vErrs++dErrs) spec
              ) specsDefs
    where
        -- Grupo de declaraciones de un módulos mas las de sus imports
        dswi :: Declarations 
        dswi = maybe ds (concatDeclarations ds) imds
        specsDefs :: [(DeclPos,SpecDecl)]
        specsDefs = specs ds

checkFuns :: Declarations -> Maybe Declarations -> 
             [Either (ErrInDecl FunDecl) FunDecl]
checkFuns ds imds = 
    L.map (\(dPos,fun) -> 
    case (checkDefVar fun dswi, checkDoubleDef CDFun (dPos,fun) dswi, checkIsPrg fun) of
        ([],[],True) -> Right fun
        (vErrs,dErrs,isP) -> Left $ ErrInDecl dPos (makeError isP (vErrs ++ dErrs)) fun
          ) funsDefs
    where
        -- Grupo de declaraciones de un módulos mas las de sus imports
        dswi :: Declarations 
        dswi = maybe ds (concatDeclarations ds) imds
        funsDefs :: [(DeclPos,FunDecl)]
        funsDefs = functions ds
        makeError :: Bool -> [DeclError] -> [DeclError]
        makeError isP errs = if isP 
                                then errs
                                else errs ++ [InvalidPrgDeclaration] 

checkThm :: Declarations -> Maybe Declarations ->
            [Either (ErrInDecl ThmDecl) ThmDecl]
checkThm ds imds = 
        L.foldl (\prevThms (dPos,thm@(Thm p)) -> 
            do
            let (errThms,rThms) = partitionEithers prevThms
            let proofWithDecls = addDeclHypothesis ds (rThms ++ imThms) imds (thProof p)
            case (checkDoubleDef CDThm (dPos,thm) dswi, validateProof proofWithDecls) of
                ([],Right _) -> Right thm : prevThms
                (dErrs,eiErrs) -> (Left $ ErrInDecl dPos (dErrs++makeError eiErrs) thm) : prevThms
                ) [] thmDefs
    where
        imThms :: [ThmDecl]
        imThms = maybe [] (map snd . theorems) imds
        -- Grupo de declaraciones de un módulos mas las de sus imports
        dswi :: Declarations 
        dswi = maybe ds (concatDeclarations ds) imds
        thmDefs :: [(DeclPos,ThmDecl)]
        thmDefs = reverse $ theorems ds
        makeError :: Either ProofError Proof -> [DeclError]
        makeError = either (\p -> [InvalidProofForThm p]) (const [])

hypListFromDeclarations :: Declarations -> [ThmDecl] -> [Hypothesis]
hypListFromDeclarations decls thms = 
    let (hSpecs,hFuns,hProps,hVals) = 
          (hyps specs decls,hyps functions decls,hyps vals decls, hyps props decls) in
          
        L.concat [hSpecs,hFuns,hProps,hVals,hThms]
    
    where hyps :: Decl d => (Declarations -> [(a,d)]) -> Declarations -> [Hypothesis]
          hyps f ds = mapMaybe (createHypDecl . snd) $ f ds
          hThms :: [Hypothesis]
          hThms = mapMaybe createHypDecl thms
        
-- Esta funcion agrega a una prueba las hipótesis correspondientes a todas las declaraciones
-- definidas y los teoremas validos.
addDeclHypothesis :: Declarations -> [ThmDecl] -> Maybe Declarations -> Proof -> Proof
addDeclHypothesis decls validThms mImportDecls pr =
    addDeclsHyps pr
    
    where imThms :: [ThmDecl]
          imThms = maybe [] (map snd . theorems) mImportDecls
          addDeclsHyps :: Proof -> Proof
          addDeclsHyps p = 
            L.foldl (\p hyp -> fromJust $ addDeclsHyp p hyp) 
                    p (hypListFromDeclarations dswi validThms)
          addDeclsHyp :: Proof -> Hypothesis -> Maybe Proof
          addDeclsHyp p hyp = do
                    ctx <- getCtx p
                    let updateCtx = addHypothesis' hyp ctx
                    setCtx updateCtx p
          dswi :: Declarations 
          dswi = maybe decls (concatDeclarations decls) mImportDecls

        
checkVals :: Declarations -> Maybe Declarations ->
             [Either (ErrInDecl ValDecl) ValDecl]
checkVals ds imds =  
            L.map (\(dPos,val) -> 
                case (checkDefVar val dswi,checkDoubleDef CDVal (dPos,val) dswi) of
                    ([],[])-> Right val
                    (vErrs,dErrs) -> Left $ ErrInDecl dPos (vErrs++dErrs) val) valsDefs
    where
        -- Grupo de declaraciones de un módulos mas las de sus imports
        dswi :: Declarations 
        dswi = maybe ds (concatDeclarations ds) imds
        valsDefs :: [(DeclPos,ValDecl)]
        valsDefs = vals ds
        funDefs :: [(DeclPos,FunDecl)]
        funDefs = functions ds

checkDefVar :: Decl d => d -> Declarations -> [DeclError]
checkDefVar d ds = lefts $ 
            L.map (\v -> 
                    if v `L.elem` (valsDef ds ++ funcsDef ds ++ argsVarsDef)
                    then Right ()
                    else Left $ NotInScopeVar v) (S.toList $ PE.freeVars $ getFocusDecl d)
    where
        argsVarsDef :: [Variable]
        argsVarsDef = fromMaybe [] $ getVarsDecl d

getFocusDecl :: Decl d => d -> PE.PreExpr
getFocusDecl = fromJust . getExprDecl 

checkIsPrg :: Decl d => d -> Bool
checkIsPrg = isPrg . fromJust . getExprDecl

checkDoubleDef :: (Decl d,Eq d) => CDoubleType -> (DeclPos,d) -> 
                                   Declarations -> [DeclError]
checkDoubleDef cdType (dPos,decl) ds = 
                whenL (cdType /= CDSpec) (checkDoubleDef' funsDefs) ++
                whenL (cdType /= CDFun)  (checkDoubleDef' specsDefs) ++
                checkDoubleDef' valsDefs ++
                checkDoubleDef' thmsDefs ++
                checkDoubleDef' propsDefs 
    where
        whenL :: Bool -> [DeclError] -> [DeclError]
        whenL b ds = if b then ds else []
        funsDefs :: [(DeclPos,FunDecl)]
        funsDefs = functions ds
        valsDefs :: [(DeclPos,ValDecl)]
        valsDefs = vals ds
        thmsDefs :: [(DeclPos,ThmDecl)]
        thmsDefs = theorems ds
        propsDefs :: [(DeclPos,PropDecl)]
        propsDefs = props ds
        specsDefs :: [(DeclPos,SpecDecl)]
        specsDefs = specs ds
        mErr :: (Decl d, Eq d) => (DeclPos,d) -> Either DeclError d
        mErr (dPos',d') = if getNameDecl decl == getNameDecl d' && dPos /= dPos'
                            then Left $ DuplicateName $ getNameDecl decl
                            else Right d'
        checkDoubleDef' :: (Decl d, Eq d) => [(DeclPos,d)] -> [DeclError]
        checkDoubleDef' decls = lefts $ L.filter isLeft $ L.map mErr decls
        isLeft = either (const True) (const False)

initTheorems :: [Theorem]
initTheorems = concatMap theorytheorems [arithTheory,listTheory,folTheory]

mapIndTypes :: [(Type' TyVarName, IndType)]
mapIndTypes = [ (TyAtom ATyNat,natural)
              , (TyAtom ATyBool,bool)
              , (TyList (tyVar "A"), list)
              ]

emptyInDeclarations :: InvalidDeclarations
emptyInDeclarations = 
     InvalidDeclarations { inSpecs      = []
                         , inFunctions  = []
                         , inTheorems   = []
                         , inProps      = []
                         , inVals       = []
                         , inDerivs     = []
                         }

initDeclarations :: Declarations
initDeclarations = Declarations {
                    functions = []
                  , specs = []
                  , theorems = map (\t -> (initDeclPos,Thm t)) initTheorems
                  , props = []
                  , vals = []
                  , derivs = []
                  , indTypes = mapIndTypes
                }
    where
        initDeclPos = DeclPos initPosThms initPosThms (pack "")
        initPosThms = newPos "TeoremasIniciales" 0 0

modifyFunDecl :: (FunDecl -> FunDecl) -> Declarations -> Declarations
modifyFunDecl f d = d { functions = map (second f) (functions d) }
