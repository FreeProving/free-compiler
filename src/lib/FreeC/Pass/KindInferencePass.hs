module Freec.Pass.KindInferencePass
    (
    ) where

import qualified FreeC.IR.Syntax as IR
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pass
import           FreeC.Pretty

kindInferencePass :: Pass IR.Module
kindInferencePass = undefined

containsLeftTypeVars :: IR.Type -> Converter ()
containsLeftTypeVars (TypeVar _ _)               = return ()
containsLeftTypeVars (TypeCon _ _)               = return ()
containsLeftTypeVars (TypeApp _ (TypeVar _ _) _) = reportLeftVarError
containsLeftTypeVars (TypeApp _ lhs _)           = containsLeftTypeVars lhs
containsLeftTypeVars (FuncType _ lhs rhs)        = containsLeftTypeVars lhs ||
                                                   containsLeftTypeVars rhs
