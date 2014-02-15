module Fun.Module.Error where

import Fun.Verification
import Fun.Decl.Error
import Fun.Parser
import Fun.Derivation

import Fun.Decl (SpecDecl, FunDecl, ValDecl, ThmDecl, DerivDecl)

import Data.Text (Text,unpack)

data ModuleError = ModuleParseError TextFilePath ParseError
                 | ModuleErrorFileDoesntExist Text
                 | ModuleCycleImport [Text]
                 | ModuleError 
                    { mName :: Text
                    , mErrSpecs :: [ErrInDecl SpecDecl]
                    , mErrFuns  :: [ErrInDecl FunDecl]
                    , mErrVals  :: [ErrInDecl ValDecl]
                    , mErrThm   :: [ErrInDecl ThmDecl]
                    , mErrVer   :: [ErrInVerif Verification]
                    , mErrDeriv :: [ErrInDeriv DerivDecl]
                    , mErrTC    :: String
                    }

instance Show ModuleError where
    show (ModuleParseError fp perr) = "Error de parseo en " ++ show (unpack fp) 
                                    ++ ":\n" ++ show perr
    show (ModuleErrorFileDoesntExist t) = 
        "No existe el archivo correspondiente a este nombre de módulo: " ++ unpack t
    show (ModuleCycleImport (mn:mns)) = 
        unlines [ "Import ciclico:\n\tbegin in -> " ++ show (unpack mn)
                , foldr (\mn' s -> s ++ "\n\timport -> " ++ show (unpack mn')) "" (init mns)
                , "\tend in -> " ++ show (last mns)
                ]
    show m = unlines [ "\n=============ErrorsInModule=========="
                     , "Modulo: " ++ show (mName m)
                     , "Specs con error: " ++  show (mErrSpecs m)
                     , "Funs con error: " ++  show (mErrFuns m)
                     , "Vals con error: " ++  show (mErrVals m)
                     , "Thms con error: " ++  show (mErrThm m)
                     , "Vers con error: " ++  show (mErrVer m)
                     , "Ders con error : " ++ show (mErrDeriv m)
                     , "Errores en el type-checking : " ++ mErrTC m
                     , "===================================="
                     ]

instance Eq ModuleError where
    ModuleParseError _ _ == ModuleParseError _ _ = error "Impossible"
    m == m' = mName m == mName m' &&
              mErrSpecs m == mErrSpecs m' &&
              mErrFuns m == mErrFuns m' &&
              mErrVals m == mErrVals m' &&
              mErrThm m == mErrThm m' &&
              mErrVer m == mErrVer m'

createError :: Text -> ([ErrInDecl SpecDecl], [ErrInDecl FunDecl], 
                [ErrInDecl ValDecl], [ErrInDecl ThmDecl], 
                [ErrInVerif Verification],[ErrInDeriv DerivDecl],String)  ->
                ModuleError
createError name (errSpecs, errFuns, errVals, errThm, errVer,errDeriv,tcErr) = 
                ModuleError name errSpecs errFuns errVals errThm errVer errDeriv tcErr
