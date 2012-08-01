
module Fun.Declarations where

import Equ.Syntax hiding (Func)
import qualified Equ.PreExpr as PE ( toFocus, PreExpr'(Var)
                                   , listOfVar, Focus)
import Equ.Proof
import Equ.Types

import Fun.Theories
import Fun.Theory
import Fun.Decl
import Fun.Decl.Error
import Equ.IndType

import qualified Data.Map as M
import Data.Text hiding (map,concatMap,unlines)
import qualified Data.List as L (map,elem,delete,filter)
import Data.Either (lefts)
import Data.Maybe (fromJust,fromMaybe)
import Text.Parsec.Pos

data DeclPos = DeclPos { begin :: SourcePos
                       , end   :: SourcePos
                       }
    deriving Show

data Declarations = Declarations {
                   specs     :: [(DeclPos,SpecDecl)]
                 , functions :: [(DeclPos,FunDecl)]
                 , theorems  :: [(DeclPos,ThmDecl)]
                 , props     :: [(DeclPos,PropDecl)]
                 , vals      :: [(DeclPos,ValDecl)]
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
                            (indTypes d ++ indTypes d')

instance Show Declarations where
    show decls = unlines [ ""
                         , "Specs: " ++ show (specs decls)
                         , "Funs:  " ++ show (functions decls) 
                         , "Thms:  " ++ show (theorems decls) 
                         , "Props: " ++ show (props decls) 
                         , "Vals:  " ++ show (vals decls)
                         ]
            
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

valsDef :: Declarations -> [Variable]
valsDef = L.map (\(_,Val v _) -> v) . vals

funcsDef :: Declarations -> [Variable]
funcsDef = L.map (\(_,Fun f _ _ _) -> f) . functions

checkSpecs :: Declarations -> [Either (ErrInDecl SpecDecl) SpecDecl]
checkSpecs ds = checkDoubleDef specsDefs mErr ++ L.map checkSpec specsDefs
    where
        checkSpec spec = case checkDefVar spec ds ++ checkDefFunc spec ds of
                           [] -> Right spec
                           errors -> Left (errors,spec)
        specsDefs :: [SpecDecl]
        specsDefs = map snd $ specs ds
        mErr :: SpecDecl -> Either (ErrInDecl SpecDecl) SpecDecl
        mErr spec@(Spec f _ _) = if spec `L.elem` L.delete spec specsDefs
                                    then Left ([MultipleDeclaredFunc f],spec)
                                    else Right spec
                    
checkFuns :: Declarations -> [Either (ErrInDecl FunDecl) FunDecl]
checkFuns ds = 
    checkDoubleDef funsDefs mErr ++
    L.map (\fun -> 
    case (checkDefVar fun ds, checkDefFunc fun ds, checkIsPrg  fun) of
        ([],[],True) -> Right fun
        (vErrs,fErrs,isP) -> Left $ if isP 
                                  then (vErrs ++ fErrs, fun)
                                  else (vErrs ++ fErrs ++ [InvalidPrgDeclaration], fun)
          ) funsDefs
    where
        funsDefs :: [FunDecl]
        funsDefs = map snd $ functions ds
        mErr :: FunDecl -> Either (ErrInDecl FunDecl) FunDecl
        mErr fun@(Fun f _ _ _) = if fun `L.elem` L.delete fun funsDefs
                                    then Left ([MultipleDeclaredFunc f],fun)
                                    else Right fun

checkThm :: Declarations -> [Either (ErrInDecl ThmDecl) ThmDecl]
checkThm ds =  checkDoubleDef thmDefs mErr ++
            L.map (\thm@(Thm p) -> 
            either (\p -> Left ([InvalidProofForThm p],thm)) (const $ Right thm) 
                (validateProof (thProof p))) thmDefs
    where
        thmDefs :: [ThmDecl]
        thmDefs = map snd $ theorems ds
        mErr :: ThmDecl -> Either (ErrInDecl ThmDecl) ThmDecl
        mErr thm = if thm `L.elem` L.delete thm thmDefs
                    then Left ([MultipleDeclaredThm $ getNameDecl thm],thm)
                    else Right thm

checkVals :: Declarations -> [Either (ErrInDecl ValDecl) ValDecl]
checkVals ds =  checkDoubleDef valsDefs mErr ++
                L.map (\val -> 
                case (checkDefVar val ds, checkDefFunc val ds) of
                    ([],[]) -> Right val
                    (vErrs,fErrs) -> Left (vErrs ++ fErrs, val)) valsDefs
    where
        valsDefs :: [ValDecl]
        valsDefs = map snd $ vals ds
        funDefs :: [FunDecl]
        funDefs = map snd $ functions ds
        mErr :: ValDecl -> Either (ErrInDecl ValDecl) ValDecl
        mErr val@(Val v _) = if val `L.elem` L.delete val valsDefs
                                then Left ([MultipleDeclaredVar v],val)
                                else Right val

checkDoubleDef :: (Decl d, Eq d) => [d] -> (d -> Either (ErrInDecl d) d) -> 
                                    [Either (ErrInDecl d) d]
checkDoubleDef decls mErr = L.filter isLeft $ L.map mErr decls
    where isLeft = either (const True) (const False)

checkDefVar :: Decl d => d -> Declarations -> [DeclError]
checkDefVar d ds = lefts $ 
            L.map (\(PE.Var v, _) -> 
                    if v `L.elem` (valsDef ds ++ argsVarsDef)
                    then Right ()
                    else Left $ UndeclaredVar v) (PE.listOfVar $ getFocusDecl d)
    where
        argsVarsDef :: [Variable]
        argsVarsDef = fromMaybe [] $ getVarsDecl d

checkDefFunc :: Decl d => d -> Declarations -> [DeclError]
checkDefFunc d ds = lefts $
            L.map (\(PE.Var f, _) -> 
                    if f `L.elem` funcsDef ds
                    then Right ()
                    else Left $ UndeclaredFunc f) (PE.listOfVar $ getFocusDecl d)

getFocusDecl :: Decl d => d -> PE.Focus
getFocusDecl = PE.toFocus . fromJust . getExprDecl 

checkIsPrg :: Decl d => d -> Bool
checkIsPrg = isPrg . fromJust . getExprDecl

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
                  , indTypes = mapIndTypes
                }
    where
        initDeclPos = DeclPos initPosThms initPosThms
        initPosThms = newPos "TeoremasIniciales" 0 0
        