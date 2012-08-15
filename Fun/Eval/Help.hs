module Fun.Eval.Help where

import Equ.PreExpr(PreExpr,toExpr)
import Fun.Eval.EvalMonad

import Data.Monoid
import Data.List (intersperse)

import Control.Applicative((<$>))

-- | Dado la forma de escribir algo parseable y la descripción, lo muestra
-- de una manera "bonita".
fmtHelp :: ParseInfo -> String
fmtHelp (ParseInfo (concrete,info)) = fmtPars concrete ++ "\n\t" ++ info

fmtPars :: Parseable -> String
fmtPars (Simple str) = str
fmtPars (Alts ps) = braces $ concat $ intersperse " | " $ map fmtPars ps
    where braces str = "[" ++ str ++ "]"
fmtPars (Seq ps) = concat $ intersperse " " $ map fmtPars ps

type Description = String
data Parseable = Simple String
               | MetaVar String 
               | Alts [Parseable]
               | Seq [Parseable]

newtype ParseInfo = ParseInfo (Parseable,Description)

alts :: [String] -> Parseable
alts = Alts . map Simple
seqs = Seq . map Simple

class Parse a where
    info :: a -> ParseInfo

mkPInfo = curry ParseInfo

instance Show Query where
    show = fmtHelp . info

instance Parse Param where
    info (Order _) = mkPInfo (alts ["eager","normal"])
                             "Orden de evaluación"

instance Parse Query where
    info QOrder = mkPInfo (Simple "order") 
                          "Orden de evaluación"
    info QCurrentProof = mkPInfo (Simple "proof")
                                 "La prueba construida hasta este momento"
    info QCurrentEnv = mkPInfo (Simple "env")
                               "Las funciones del entorno actual"
    info QInitExpr = mkPInfo (Simple "expr")
                             "La expresión inicial de la evaluación actual"
    info QLastResult = mkPInfo (Simple "result")
                               "El resultado del último paso"

instance Show EvCmd where
    show = fmtHelp . info

instance Parse EvCmd where
    info Reset = mkPInfo (Simple "reset")                  
                 "Descarta la evaluación actual y recarga el entorno."
    info (Set p) = let ParseInfo (pRepr,pDesc) = info p
                   in mkPInfo (Seq [Simple ":set", pRepr])
                          $ "Define el parámetro " ++ pDesc
    info (Step _) = mkPInfo (seqs ["step","/expr/"]) 
                    "Comienza la evaluación paso a paso de la expresión."
    info (Trace _) = mkPInfo (seqs ["trace","/expr/"]) 
                     "Como step pero mostrando cada resultado intermedio."
    info (Eval _) = mkPInfo (seqs ["eval","/expr/"]) 
                    "Evalúa la expresión hasta su forma canónica."
    info Next = mkPInfo (Simple "next")
                "Continua con la evaluación actual, si hay alguna."
    info (Show _) = mkPInfo (seqs ["show","/expr/"])
                    "Muestra la expresión (útil para ver si una expresión está bien tipada)."
    info (Get q) = let ParseInfo (pRepr,pDesc) = info q
                   in mkPInfo (Seq [Simple "get", pRepr])
                          $ "Muestra información sobre el parámetro" ++ pDesc
    info Help = mkPInfo (alts ["help","help /cmd/"])
                $ "Los comandos disponibles son: \n" ++ unlines (map ("\t"++) cmdList)

cmdList = [ "reset"
          , "set"
          , "step"
          , "trace"
          , "eval"
          , "next"
          , "show"
          , "get"
          , "help"
          ]
