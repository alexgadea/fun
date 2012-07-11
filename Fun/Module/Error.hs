module Fun.Module.Error where

import Fun.Derivation.Error
import Fun.Decl.Error
import Fun.Parser

import Fun.Decl (SpecDecl, FunDecl, ValDecl, ThmDecl)

data ModuleError = ModuleParseError ParseError
                 | ModuleError 
                    { mErrSpecs :: [ErrInDecl SpecDecl]
                    , mErrFuns  :: [ErrInDecl FunDecl]
                    , mErrVals  :: [ErrInDecl ValDecl]
                    , mErrThm   :: [ErrInDecl ThmDecl]
                    , mErrDer   :: [DerivationError]
                    }

instance Show ModuleError where
    show (ModuleParseError perr) = show perr
    show m = "\nSpecs con error: " ++  show (mErrSpecs m) ++
             "\nFuns con error: " ++  show (mErrFuns m) ++
             "\nVals con error: " ++  show (mErrVals m) ++
             "\nThm con error: " ++  show (mErrThm m) ++
             "\nDer con error: " ++  show (mErrDer m)
             
    

instance Eq ModuleError where
    ModuleParseError p == ModuleParseError p' = error "Impossible"
    m == m' = mErrSpecs m == mErrSpecs m' &&
              mErrFuns m == mErrFuns m' &&
              mErrVals m == mErrVals m' &&
              mErrThm m == mErrThm m' &&
              mErrDer m == mErrDer m'

createError :: ([ErrInDecl SpecDecl], [ErrInDecl FunDecl], 
                [ErrInDecl ValDecl], [ErrInDecl ThmDecl], 
                [DerivationError]) -> ModuleError
createError (errSpecs, errFuns, errVals, errThm, errDer) = 
                ModuleError errSpecs errFuns errVals errThm errDer
