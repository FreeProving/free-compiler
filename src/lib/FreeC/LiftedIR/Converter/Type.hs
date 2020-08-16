-- | Implements the IR to lifted IR translation, which applies the monadic
--   lifting as described by Abel et al. in "Verifying Haskell Programs Using
--   Constructive Type Theory".
module FreeC.LiftedIR.Converter.Type
  ( liftFuncArgTypes
  , liftConArgType
  , liftVarPatType
    -- * Translations
  , liftType
  , liftType'
  ) where

import           Data.Bool ( bool )

import           FreeC.IR.SrcSpan ( SrcSpan(NoSrcSpan) )
import qualified FreeC.IR.Syntax as IR
import qualified FreeC.LiftedIR.Syntax as LIR
import           FreeC.Monad.Converter ( Converter )
import           FreeC.Monad.Reporter
  ( Message(Message), Severity(Error, Internal), reportFatal )

-- | Converts the argument types of a function.
liftFuncArgTypes
  :: Maybe Int -- ^ Index of the decreasing argument for recursive functions.
  -> [IR.VarPat] -- ^ The argument types.
  -> Converter [LIR.Type]
liftFuncArgTypes = maybe liftNonRecFuncArgTypes liftRecFuncArgTypes

-- | Converts the argument types of a non recursive function using
--   @convertType@.
liftNonRecFuncArgTypes :: [IR.VarPat] -> Converter [LIR.Type]
liftNonRecFuncArgTypes = mapM
  $ \pat -> let err = reportFatal
                  $ Message (IR.varPatSrcSpan pat) Internal
                  $ "Expected variable pattern to have a type annotation."
            in liftVarPatType pat >>= maybe err return

-- | Converts the argument types of a recursive function using @convertType@.
--
--   The outermost argument at the given index is marked decreasing.
liftRecFuncArgTypes :: Int -> [IR.VarPat] -> Converter [LIR.Type]
liftRecFuncArgTypes decIndex args = do
  convArgs <- liftNonRecFuncArgTypes args
  let (startArgs, decArg : endArgs) = splitAt decIndex convArgs
  decArg' <- markOutermostDecreasing decArg
  return $ startArgs ++ (decArg' : endArgs)

-- | Lifts the type of an 'IR.VarPat'. If the argument is strict the type itself
--   isn't lifted into the @Free@ monad.
liftVarPatType :: IR.VarPat -> Converter (Maybe LIR.Type)
liftVarPatType (IR.VarPat _ _ patType strict) = mapM
  (bool liftType liftType' strict) patType

-- | Converts a constructor argument using @convertType@.
--
--   All occurrences of the constructed type are marked as structurally smaller.
liftConArgType :: IR.QName -> IR.Type -> Converter LIR.Type
liftConArgType ident t = markAllDec ident <$> liftType t

-------------------------------------------------------------------------------
-- Translations                                                              --
-------------------------------------------------------------------------------
-- | Converts a type from IR to lifted IR by lifting it into the @Free@ monad.
--
--   This corresponds to the dagger translation for monotypes as described by
--   Abel et al.
--
--   > τ' = Free τ*
liftType :: IR.Type -> Converter LIR.Type
liftType t = LIR.FreeTypeCon NoSrcSpan <$> liftType' t

-- | Lifts a type from IR to lifted IR by adding the free arguments to
--   constructors and lifting function types in the @Free@ monad.
--
--   This corresponds to the star translation for monotypes as described by
--   Abel et al.
--
liftType' :: IR.Type -> Converter LIR.Type
liftType' = flip liftTypeApp' []

-- | Like 'liftType'' but accumulates the type arguments in a second parameter.
--
--   > (C τ₁ … τₙ)* = C τ₁* … τₙ*
--   > (τ₁ -> τ₂)* = τ₁' -> τ₂'
--   > α* = α
liftTypeApp' :: IR.Type -> [IR.Type] -> Converter LIR.Type
liftTypeApp' (IR.TypeCon srcSpan name) ts
  = LIR.TypeCon srcSpan name <$> mapM liftType' ts <*> return False
liftTypeApp' (IR.TypeVar srcSpan name) [] = return $ LIR.TypeVar srcSpan name
liftTypeApp' (IR.TypeApp _ l r) ts = liftTypeApp' l (r : ts)
liftTypeApp' (IR.FuncType srcSpan l r) []
  = LIR.FuncType srcSpan <$> liftType l <*> liftType r
liftTypeApp' _ (_ : _) = reportFatal
  $ Message NoSrcSpan Internal
  $ "Only type constructors can be applied!"

-------------------------------------------------------------------------------
-- Helper Functions for Decreasing Arguments                                 --
-------------------------------------------------------------------------------
-- | Marks all occurrences of type constructors with the given name as
--   decreasing.
markAllDec :: LIR.TypeConName -> LIR.Type -> LIR.Type
markAllDec _ (LIR.TypeVar srcSpan name)              = LIR.TypeVar srcSpan name
markAllDec decName (LIR.FuncType srcSpan l r)        = LIR.FuncType srcSpan
  (markAllDec decName l) (markAllDec decName r)
markAllDec decName (LIR.FreeTypeCon srcSpan t)
  = LIR.FreeTypeCon srcSpan $ markAllDec decName t
markAllDec decName (LIR.TypeCon srcSpan name ts dec) = LIR.TypeCon srcSpan name
  (markAllDec decName `fmap` ts) (name == decName || dec)

-- | Marks the outermost occurring type constructor as decreasing.
--
--   Note: Could be generalized to annotate a constructor based on a position.
--   At the moment this isn't needed because our termination checker doesn't
--   cover cases where the decreasing argument is part of another argument.
--   For example, a decreasing argument in the first element of a pair is not
--   covered.
markOutermostDecreasing :: LIR.Type -> Converter LIR.Type
markOutermostDecreasing (LIR.TypeCon srcSpan name ts _)
  = return $ LIR.TypeCon srcSpan name ts True
markOutermostDecreasing (LIR.FreeTypeCon srcSpan t)
  = LIR.FreeTypeCon srcSpan <$> markOutermostDecreasing t
markOutermostDecreasing _ = reportFatal
  $ Message NoSrcSpan Error
  $ "Outermost type of decreasing argument is not a "
  ++ "type constructor application."
