
module Fun.Declarations where

import Equ.Syntax hiding (Func)
import qualified Equ.PreExpr as PE (PreExpr, freeVars)
import Equ.Proof
import Equ.Types

import Fun.Theories
import Fun.Theory
import Fun.Decl
import Fun.Decl.Error
import Equ.IndType

import qualified Data.List as L (map,elem,delete,filter,concatMap)
import qualified Data.Set as S (toList)
import qualified Data.Map as M
import Data.Text hiding (map,concatMap,unlines)
import Data.Either (lefts)
import Data.Maybe (fromJust,fromMaybe)

import Text.Parsec.Pos (newPos)

import Control.Monad

data CDoubleType = CDSpec | CDFun | CDThm | CDProp | CDVal
    deriving Eq

data Declarations = Declarations {
                   specs     :: [(DeclPos,SpecDecl)]
                 , functions :: [(DeclPos,FunDecl)]
                 , theorems  :: [(DeclPos,ThmDecl)]
                 , props     :: [(DeclPos,PropDecl)]
                 , vals      :: [(DeclPos,ValDecl)]
                 , derivs    :: [(DeclPos,DerivDecl)]
                 , indTypes  :: [(Type,IndType)] -- Si luego extendemos para declarar tipos, este campo del environment va agregando cada uno de
                                           -- los nuevos tipos declarados. Por ahora usaremos solo el valor inicial que le pasamos,
                                           -- el cual contiene los tipos basicos de Equ.
            }

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

checkSpecs :: Declarations -> [Either (ErrInDecl SpecDecl) SpecDecl]
checkSpecs ds = 
        L.map (\(dPos,spec) ->
            case (checkDefVar spec ds, checkDoubleDef CDSpec (dPos,spec) ds) of
                ([],[]) -> Right spec
                (vErrs,dErrs) -> Left $ ErrInDecl dPos (vErrs++dErrs) spec
              ) specsDefs
    where
        specsDefs :: [(DeclPos,SpecDecl)]
        specsDefs = specs ds

checkFuns :: Declarations -> [Either (ErrInDecl FunDecl) FunDecl]
checkFuns ds = 
    L.map (\(dPos,fun) -> 
    case (checkDefVar fun ds, checkDoubleDef CDFun (dPos,fun) ds, checkIsPrg fun) of
        ([],[],True) -> Right fun
        (vErrs,dErrs,isP) -> Left $ ErrInDecl dPos (makeError isP (vErrs ++ dErrs)) fun
          ) funsDefs
    where
        funsDefs :: [(DeclPos,FunDecl)]
        funsDefs = functions ds
        makeError :: Bool -> [DeclError] -> [DeclError]
        makeError isP errs = if isP 
                                then errs
                                else errs ++ [InvalidPrgDeclaration] 

checkThm :: Declarations -> [Either (ErrInDecl ThmDecl) ThmDecl]
checkThm ds = 
        L.map (\(dPos,thm@(Thm p)) -> 
            case (checkDoubleDef CDThm (dPos,thm) ds, validateProof (thProof p)) of
                ([],Right _) -> Right thm
                (dErrs,eiErrs) -> Left $ ErrInDecl dPos (dErrs++makeError eiErrs) thm
              ) thmDefs
    where
        thmDefs :: [(DeclPos,ThmDecl)]
        thmDefs = theorems ds
        makeError :: Either ProofError Proof -> [DeclError]
        makeError = either (\p -> [InvalidProofForThm p]) (const [])

checkVals :: Declarations -> [Either (ErrInDecl ValDecl) ValDecl]
checkVals ds =  L.map (\(dPos,val) -> 
                case (checkDefVar val ds,checkDoubleDef CDVal (dPos,val) ds) of
                    ([],[])-> Right val
                    (vErrs,dErrs) -> Left $ ErrInDecl dPos (vErrs++dErrs) val) valsDefs
    where
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
