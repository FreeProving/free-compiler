module FreeC.Frontend where

import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Reporter

data Frontend = Frontend
  { name      :: String
  , parseFile :: SrcFile -> Reporter IR.Module
  }
