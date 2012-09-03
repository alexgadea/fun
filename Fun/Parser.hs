-- | Parser general de fun.
module Fun.Parser 
            ( module Fun.Parser.Module
            , module Fun.Parser.Internal
            , module Text.Parsec
            )
    where

import Fun.Parser.Module
import Fun.Parser.Internal
import Text.Parsec