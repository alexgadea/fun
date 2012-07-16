module Fun.Theories (
      module Fun.FunTheories.Arith
    , module Fun.FunTheories.List
    , module Fun.FunTheories.FOL
    , funTheory
    )
    where


import Fun.FunTheories.Arith
import Fun.FunTheories.List
import Fun.FunTheories.FOL


funTheory = [arithTheory,folTheory,listTheory]