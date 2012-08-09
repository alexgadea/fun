module Fun.Module.Error where

import Fun.Derivation
import Fun.Derivation.Error
import Fun.Decl.Error
import Fun.Parser

import Fun.Decl (SpecDecl, FunDecl, ValDecl, ThmDecl)

import Data.Text (Text,unpack)

data ModuleError = ModuleParseError ParseError
                 | ModuleErrorFileDoesntExist Text
                 | ModuleCycleImport [Text]
                 | ModuleError 
                    { mName :: Text
                    , mErrSpecs :: [ErrInDecl SpecDecl]
                    , mErrFuns  :: [ErrInDecl FunDecl]
                    , mErrVals  :: [ErrInDecl ValDecl]
                    , mErrThm   :: [ErrInDecl ThmDecl]
                    , mErrDer   :: [ErrInDeriv Derivation]
                    }

instance Show ModuleError where
    show (ModuleParseError perr) = show perr
    show (ModuleErrorFileDoesntExist t) = 
        "No existe el archivo correspondiente a este nombre de módulo: " ++ unpack t
    show (ModuleCycleImport (mn:mns)) = 
        unlines [ "Import ciclico:\n\tbegin in -> " ++ show (unpack mn)
                , foldr (\mn s -> s ++ "\n\timport -> " ++ show (unpack mn)) "" (init mns)
                , "\tend in -> " ++ show (last mns)
                ]
    show m = unlines [ "\n=============ErrorsInModule=========="
                     , "Modulo: " ++ show (mName m)
                     , "Specs con error: " ++  show (mErrSpecs m)
                     , "Funs con error: " ++  show (mErrFuns m)
                     , "Vals con error: " ++  show (mErrVals m)
                     , "Thm con error: " ++  show (mErrThm m)
                     , "Der con error: " ++  show (mErrDer m)
                     , "===================================="
                     ]

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
                [ErrInDeriv Derivation]) -> ModuleError
createError name (errSpecs, errFuns, errVals, errThm, errDer) = 
                ModuleError name errSpecs errFuns errVals errThm errDer
