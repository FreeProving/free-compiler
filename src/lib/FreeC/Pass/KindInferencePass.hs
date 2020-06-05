module Freec.Pass.KindInferencePass
    (
    ) where

import qualified FreeC.IR.Syntax as IR


kindInferencePass :: Pass IR.Module
kindInferencePass = undefined

containsLeftTypeVars :: IR.Type -> Bool
containsLeftTypeVars (TypeVar _ _)               = False
containsLeftTypeVars (TypeCon _ _)               = False
containsLeftTypeVars (TypeApp _ (TypeVar _ _) _) = True
containsLeftTypeVars (TypeApp _ lhs _)           = containsLeftTypeVars lhs
containsLeftTypeVars (FuncType _ lhs rhs)        = containsLeftTypeVars lhs ||
                                                   containsLeftTypeVars rhs
