module Fun.Module.Error where

import Fun.Derivation.Error
import Fun.Decl.Error
import Fun.Parser

import Fun.Decl (SpecDecl, FunDecl, ValDecl, ThmDecl)

import Data.Text (Text,unpack)

data ModuleError = ModuleParseError ParseError
                 | ModuleCycleImport [Text]
                 | ModuleError 
                    { mName :: Text
                    , mErrSpecs :: [ErrInDecl SpecDecl]
                    , mErrFuns  :: [ErrInDecl FunDecl]
                    , mErrVals  :: [ErrInDecl ValDecl]
                    , mErrThm   :: [ErrInDecl ThmDecl]
                    , mErrDer   :: [DerivationError]
                    }

instance Show ModuleError where
    show (ModuleParseError perr) = show perr
    show (ModuleCycleImport (mn:mns)) =
        "\nImport ciclico:\n\tbegin in -> " ++ show (unpack mn) ++
        (foldr (\mn s -> s ++ "\n\timport -> " ++ show (unpack mn)) "" (init mns)) ++ 
        "\n\tend in -> " ++ (show $ last mns) ++ "\n"
    show m = "\n=============ErrorsInModule==========\n" ++
             "Modulo: " ++ show (mName m) ++
             "\nSpecs con error: " ++  show (mErrSpecs m) ++
             "\nFuns con error: " ++  show (mErrFuns m) ++
             "\nVals con error: " ++  show (mErrVals m) ++
             "\nThm con error: " ++  show (mErrThm m) ++
             "\nDer con error: " ++  show (mErrDer m) ++
             "\n====================================\n"

instance Eq ModuleError where
    ModuleParseError p == ModuleParseError p' = error "Impossible"
    m == m' = mName m == mName m' &&
              mErrSpecs m == mErrSpecs m' &&
              mErrFuns m == mErrFuns m' &&
              mErrVals m == mErrVals m' &&
              mErrThm m == mErrThm m' &&
              mErrDer m == mErrDer m'

createError :: Text -> ([ErrInDecl SpecDecl], [ErrInDecl FunDecl], 
                [ErrInDecl ValDecl], [ErrInDecl ThmDecl], 
                [DerivationError]) -> ModuleError
createError name (errSpecs, errFuns, errVals, errThm, errDer) = 
                ModuleError name errSpecs errFuns errVals errThm errDer
