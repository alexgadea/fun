{-# Language TemplateHaskell, ViewPatterns #-}
module Fun.Declarations where

import Equ.Syntax hiding (Func)
import qualified Equ.PreExpr as PE (PreExpr, freeVars)
import Equ.Proof hiding (setCtx, getCtx)
import Equ.Proof.Proof
import Equ.Types

import Fun.Theories
import Fun.Theory
import Fun.Decl
import Fun.Decl.Error
import Fun.Derivation.Error
import Equ.IndType

import qualified Data.List as L
import qualified Data.Set as S 
import Data.Text hiding (map,concatMap,unlines,reverse,foldl)
import Data.Either (partitionEithers)
import Data.Maybe (fromJust,fromMaybe,mapMaybe)
import Data.Monoid
import Text.Parsec.Pos (newPos)
import Control.Arrow(second,(&&&))

import Control.Monad.Trans.State
import Control.Lens

type Annot a = (DeclPos,a)

data DefDuplicated = DSpec | DFun | DThm | DProp | DVal
    deriving Eq

class Duplicated d where
    dupName :: d -> DefDuplicated

instance Duplicated SpecDecl where
    dupName _ = DSpec

instance Duplicated FunDecl where
    dupName _ = DFun

instance Duplicated ThmDecl where
    dupName _ = DThm

instance Duplicated PropDecl where
    dupName _ = DProp

instance Duplicated ValDecl where
    dupName _ = DVal

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
    Declarations { _specs     :: [Annot SpecDecl]
                 , _functions :: [Annot FunDecl]
                 , _theorems  :: [Annot ThmDecl]
                 , _props     :: [Annot PropDecl]
                 , _vals      :: [Annot ValDecl]
                 , _derivs    :: [Annot DerivDecl]
                 , _indTypes  :: [(Type,IndType)] -- Si luego extendemos para declarar tipos, este campo del environment va agregando cada uno de
                                           -- los nuevos tipos declarados. Por ahora usaremos solo el valor inicial que le pasamos,
                                           -- el cual contiene los tipos basicos de Equ.
                 }


$(makeLenses ''Declarations)

bare :: Getting [Annot d] Declarations [Annot d] -> Declarations -> [d]
bare f = map snd . (^. f)

bareThms = bare theorems

instance Monoid Declarations where
    mempty = Declarations [] [] [] [] [] [] []
    mappend d' = execState $ do specs     %= (++ (d' ^. specs )) ;
                                functions %= (++ (d' ^. functions)) ;
                                theorems  %= (++ (d' ^. theorems))  ;
                                props     %= (++ (d' ^. props));
                                vals      %= (++ (d' ^. vals));
                                derivs    %= (++ (d' ^. derivs));
                                indTypes  %= (++ (d' ^. indTypes))

filterValidDecls :: Declarations -> InvalidDeclarations -> Declarations                 
filterValidDecls vds ivds = 
             Declarations
                (L.filter (`notIn` (inSpecs ivds)) $ _specs vds)
                (L.filter (`notIn` (inFunctions ivds)) $ _functions vds)
                (L.filter (`notIn` (inTheorems ivds)) $ _theorems vds)
                (L.filter (`notIn` (inProps ivds)) $ _props vds)
                (L.filter (`notIn` (inVals ivds)) $ _vals vds)
                (L.filter (`notIn'` (inDerivs ivds)) $ _derivs vds)
                []
    where
        notIn' :: (Eq d, Decl d) => Annot d -> [ErrInDeriv d] -> Bool
        notIn' (_,d) errds = d `L.notElem` (L.map snd errds)
        notIn :: (Eq d, Decl d) => Annot d -> [ErrInDecl d] -> Bool
        notIn (_,d) errds = d `L.notElem` (L.map eDecl errds)
                 

instance Show Declarations where
    show decls = unlines [ ""
                         , "Specs: "   ++ show (_specs decls)
                         , "Funs:  "   ++ show (_functions decls) 
                         , "Thms:  "   ++ show (_theorems decls) 
                         , "Props: "   ++ show (_props decls) 
                         , "Vals:  "   ++ show (_vals decls)
                         , "Derivs:  " ++ "[" ++ concatMap showDer (_derivs decls) ++ "]"
                         ]
        where
            showDer :: Annot DerivDecl -> String
            showDer (dPos, Deriv v v' fps) = 
                    "(" ++ show dPos ++ "," ++ 
                    "Deriv " ++ show v ++ " " ++
                    show v' ++ " " ++ 
                    ("[" ++ concatMap (show . fst) fps ++ "]") ++ 
                    ")"

envAddFun :: Annot FunDecl -> Declarations -> Declarations
envAddFun = over functions . (:) 

envAddSpec :: Annot SpecDecl -> Declarations -> Declarations
envAddSpec = over specs . (:) 

envAddVal :: Annot ValDecl -> Declarations -> Declarations
envAddVal = over vals . (:)

envAddTheorem :: Annot ThmDecl -> Declarations -> Declarations
envAddTheorem = over theorems . (:)

envAddProp :: Annot PropDecl -> Declarations -> Declarations
envAddProp = over props . (:)

envAddDeriv :: Annot DerivDecl -> Declarations -> Declarations
envAddDeriv = over derivs . (:)

valsDef :: Declarations -> [Variable]
valsDef = L.map ((^. valVar) . snd) . (^. vals)

funcsDef :: Declarations -> [Variable]
funcsDef = L.map ((^. funDeclName) . snd) . (^. functions)

okDecl :: (Decl d) => Annot d -> [DeclError] -> Either (ErrInDecl d) d
okDecl ann [] = Right (ann ^. _2)
okDecl ann err = Left $ ErrInDecl (ann ^. _1) err (ann ^. _2)

checkDecls :: (Decl d) =>
               Getting [Annot d] Declarations [Annot d]
                   -> Declarations
                   -> Declarations
                   -> (Declarations -> Annot d -> [DeclError])
                   -> [Either (ErrInDecl d) d]
checkDecls decl ds imds checks = over traverse (\ann -> okDecl ann $ (checks declsWithImports) ann) (ds ^. decl)
    where declsWithImports = ds <> imds

-- | Chequeo de declaración: chequeamos que no esté duplicada, además
-- de algún chequeo propio de la declaración.
checkDecl :: (Eq d,Decl d,Duplicated d) => (d -> Declarations -> [DeclError]) -> 
              Declarations -> Annot d -> [DeclError]
checkDecl chk decls ann = mconcat [ chk (ann ^. _2) , checkDoubleDef ann ] decls

-- | Chequeo de especificaciones; el único control que hacemos es que
-- todas las varibles estén declaradas.
checkSpecs :: Declarations -> Declarations -> 
              [Either (ErrInDecl SpecDecl) SpecDecl]
checkSpecs ds imds = checkDecls specs ds imds $ checkDecl checkDefVar

-- | Chequeo de funciones; además del chequeo de variables,
-- verificamos que el cuerpo sea un programa.
checkFuns :: Declarations ->  Declarations -> 
             [Either (ErrInDecl FunDecl) FunDecl]
checkFuns ds imds = checkDecls functions ds imds $ \d -> mconcat [checkDecl checkDefVar d, chkPrg]
    where
        chkPrg :: Annot FunDecl -> [DeclError]
        chkPrg (checkIsPrg . (^. _2) -> False) = [InvalidPrgDeclaration]
        chkPrg _  = []
        
-- | Chequeo de teoremas; además del chequeo de nombres duplicados,
-- verificamos que la prueba sea correcta.
checkThm :: Declarations -> Declarations ->
            [Either (ErrInDecl ThmDecl) ThmDecl]
checkThm ds imds = zip' $ foldl chkThm ([],[]) thmDefs
    where chkThm (errThms,okThms) decl@(pos,thm) = 
              case checkDoubleDef decl dswi of
                [] -> case validateProof (prfWithDecls okThms thm) of
                        Right _ -> (errThms, thm : okThms)
                        Left err  -> (ErrInDecl pos [InvalidProofForThm err] thm :errThms,okThms)
                errs -> (ErrInDecl pos errs thm : errThms, okThms)

          prfWithDecls thms (Thm p) = addDeclHypothesis ds (thms ++ bareThms imds) imds (thProof p)
        -- Grupo de declaraciones de un módulos mas las de sus imports
          dswi :: Declarations 
          dswi = ds <> imds
          thmDefs :: [Annot ThmDecl]
          thmDefs = reverse $ ds ^. theorems
          zip' (errs,oks) = map Left errs ++ map Right oks

hypListFromDecls :: Declarations -> [ThmDecl] -> [Hypothesis]
hypListFromDecls decls thms = mapMaybe createHypDecl thms <>
                              mconcat [ hyps _specs
                                      , hyps _functions
                                      , hyps _vals
                                      , hyps _props] decls 
                              
    where hyps :: Decl d => (Declarations -> [Annot d]) -> Declarations -> [Hypothesis]
          hyps f decls = mapMaybe (createHypDecl . snd) $ f decls
        
-- Esta funcion agrega a una prueba las hipótesis correspondientes a todas las declaraciones
-- definidas y los teoremas validos.
addDeclHypothesis :: Declarations -> [ThmDecl] -> Declarations -> Proof -> Proof
addDeclHypothesis decls validThms mImportDecls pr = foldl addHyps pr $ hypListFromDecls dswi validThms

    where imThms :: [ThmDecl]
          imThms = bareThms mImportDecls
          addHyps :: Proof -> Hypothesis -> Proof
          addHyps p hyp = fromJust $ addDeclsHyp p hyp
          addDeclsHyp :: Proof -> Hypothesis -> Maybe Proof
          addDeclsHyp p hyp = getCtx p >>= \ctx -> setCtx (addHypothesis' hyp ctx) p
          dswi :: Declarations 
          dswi = decls <> mImportDecls

        
checkVals :: Declarations -> Declarations ->
             [Either (ErrInDecl ValDecl) ValDecl]
checkVals ds imds = checkDecls vals ds imds $ checkDecl checkDefVar

checkDefVar :: Decl d => d -> Declarations -> [DeclError]
checkDefVar d ds = concatMap inScope . S.toList . PE.freeVars . getFocusDecl $ d
    where
        inScope :: Variable -> [DeclError]
        inScope v = if v `L.elem` vars then [] else [NotInScopeVar v]
        vars = valsDef ds ++ funcsDef ds ++ fromMaybe [] (getVarsDecl d)

getFocusDecl :: Decl d => d -> PE.PreExpr
getFocusDecl = fromJust . getExprDecl 

checkIsPrg :: Decl d => d -> Bool
checkIsPrg = isPrg . fromJust . getExprDecl


checkDoubleDef :: (Duplicated d,Decl d,Eq d) => Annot d -> 
                                   Declarations -> [DeclError]
checkDoubleDef (dPos,decl) = mconcat [ checkDoubleDef' . (^. vals)
                                     , checkDoubleDef' . (^. props)
                                     , checkDoubleDef' . (^. theorems)
                                     , whenL (dupName decl /= DSpec) . checkDoubleDef' . (^. functions)
                                     , whenL (dupName decl /= DFun) . checkDoubleDef' . (^. specs)
                                     ]
    where
        whenL :: Bool -> [DeclError] -> [DeclError]
        whenL b ds = if b then ds else []
        mErr :: (Decl d, Eq d) => Annot d -> [DeclError]
        mErr (dPos',d') = if getNameDecl decl == getNameDecl d' && dPos /= dPos'
                          then [DuplicateName $ getNameDecl decl]
                          else []
        checkDoubleDef' :: (Decl d, Eq d) => [Annot d] -> [DeclError]
        checkDoubleDef' decls = concatMap mErr decls

initThms :: [Theorem]
initThms = concatMap theorytheorems [arithTheory,listTheory,folTheory]

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
initDeclarations = flip execState mempty $ do theorems .= map (const initDeclPos &&& Thm) initThms;
                                              indTypes .= mapIndTypes
    where
        initDeclPos = DeclPos initPosThms initPosThms (pack "")
        initPosThms = newPos "TeoremasIniciales" 0 0

modifyFunDecl :: (FunDecl -> FunDecl) -> Declarations -> Declarations
modifyFunDecl f = over functions (map (second f))
