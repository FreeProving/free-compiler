module FreeC.Backend where

import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Application
import           FreeC.Monad.Reporter

data Backend = Backend
  { name          :: String
  , convertModule :: IR.Module -> Reporter String
  , fileExtension :: String
  , specialAction :: Application ()
  }
