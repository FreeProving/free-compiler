module FreeC.Pass.KindCheckPass where

import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Pass

kindCheckPass :: Pass IR.Module
kindCheckPass = return

checkType :: IR.Type -> Converter ()
checkType _ = return ()
