module Fun.Module.Error where

import Fun.Verification
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
                    , mErrVer   :: [ErrInVerif Verification]
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
                     , "Ver con error: " ++  show (mErrVer m)
                     , "===================================="
                     ]

instance Eq ModuleError where
    ModuleParseError p == ModuleParseError p' = error "Impossible"
    m == m' = mName m == mName m' &&
              mErrSpecs m == mErrSpecs m' &&
              mErrFuns m == mErrFuns m' &&
              mErrVals m == mErrVals m' &&
              mErrThm m == mErrThm m' &&
              mErrVer m == mErrVer m'

createError :: Text -> ([ErrInDecl SpecDecl], [ErrInDecl FunDecl], 
                [ErrInDecl ValDecl], [ErrInDecl ThmDecl], 
                [ErrInVerif Verification]) -> ModuleError
createError name (errSpecs, errFuns, errVals, errThm, errDer) = 
                ModuleError name errSpecs errFuns errVals errThm errDer
