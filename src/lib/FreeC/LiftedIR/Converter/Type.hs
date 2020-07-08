-- | Implements the IR to lifted IR translation, which applies the monadic lifting
--   as described by Abel et al. in "Verifying Haskell Programs Using Constructive
--   Type Theory".

module FreeC.LiftedIR.Converter.Type
  ( liftFuncArgTypes
  , liftConArgType
    -- * Translations
  , liftType
  , liftType'
  )
where

import qualified FreeC.IR.Syntax               as IR
import           FreeC.IR.SrcSpan               ( SrcSpan(NoSrcSpan) )
import qualified FreeC.LiftedIR.Syntax         as LIR

-- | Converts the argument types of a function.
liftFuncArgTypes
  :: Maybe Int -- ^ Index of the decreasing argument for recursive functions.
  -> [IR.Type] -- ^ The argument types.
  -> [LIR.Type]
liftFuncArgTypes = maybe liftNonRecFuncArgTypes liftRecFuncArgTypes

-- | Converts the argument types of a non recursive function using @convertType@.
liftNonRecFuncArgTypes :: [IR.Type] -> [LIR.Type]
liftNonRecFuncArgTypes = map liftType

-- | Converts the argument types of a recursive function using @convertType@.
--
--   The outermost argument at the given index is marked decreasing.
liftRecFuncArgTypes :: Int -> [IR.Type] -> [LIR.Type]
liftRecFuncArgTypes decIndex args =
  let convArgs                      = map liftType args
      (startArgs, decArg : endArgs) = splitAt decIndex convArgs
  in  startArgs ++ (markOutermostDecreasing decArg : endArgs)

-- | Converts a constructor argument using @convertType@.
--
--   All occurrences of the constructed type are marked as structurally smaller.
liftConArgType :: IR.QName -> IR.Type -> LIR.Type
liftConArgType ident = markAllDec ident . liftType

-------------------------------------------------------------------------------
-- Translations                                                              --
-------------------------------------------------------------------------------

-- | Converts a type from IR to lifted IR by lifting it into the @Free@ monad.
--
--   This corresponds to the dagger translation for monotypes as described by
--   Abel et al.
--
--   > τ' = Free τ*
liftType :: IR.Type -> LIR.Type
liftType = LIR.FreeTypeCon NoSrcSpan . liftType'

-- | Lifts a type from IR to lifted IR by adding the free arguments to
--   constructors and lifting function types in the @Free@ monad.
--
--   This corresponds to the star translation for monotypes as described by
--   Abel et al.
--
liftType' :: IR.Type -> LIR.Type
liftType' = flip liftTypeApp' []

-- | Like 'liftType'' but accumulates the type arguments in a second parameter.
--
--   > (C τ₁ … τₙ)* = C τ₁* … τₙ*
--   > (τ₁ -> τ₂)* = τ₁' -> τ₂'
--   > α* = α
liftTypeApp' :: IR.Type -> [IR.Type] -> LIR.Type
liftTypeApp' (IR.TypeCon srcSpan name) ts =
  LIR.TypeCon srcSpan name (map liftType' ts) False
liftTypeApp' (IR.TypeVar srcSpan name) [] = LIR.TypeVar srcSpan name
liftTypeApp' (IR.TypeApp _ l r       ) ts = liftTypeApp' l (r : ts)
liftTypeApp' (IR.FuncType srcSpan l r) [] =
  LIR.FuncType srcSpan (liftType l) (liftType r)
liftTypeApp' _ (_ : _) =
  error "liftTypeApp': Only type constructors can be applied!"

-------------------------------------------------------------------------------
-- Helper Functions for Decreasing Arguments                                 --
-------------------------------------------------------------------------------

-- | Marks all occurrences of type constructors with the given name as
--   decreasing.
markAllDec :: LIR.TypeConName -> LIR.Type -> LIR.Type
markAllDec _ (LIR.TypeVar srcSpan name) = LIR.TypeVar srcSpan name
markAllDec decName (LIR.FuncType srcSpan l r) =
  LIR.FuncType srcSpan (markAllDec decName l) (markAllDec decName r)
markAllDec decName (LIR.FreeTypeCon srcSpan t) =
  LIR.FreeTypeCon srcSpan $ markAllDec decName t
markAllDec decName (LIR.TypeCon srcSpan name ts dec) = LIR.TypeCon
  srcSpan
  name
  (markAllDec decName `fmap` ts)
  (name == decName || dec)

-- | Marks the outermost occurring type constructor as decreasing.
--
--   Note: Could be generalized to annotate a constructor based on a position.
--   At the moment this isn't needed because our termination checker doesn't
--   cover cases where the decreasing argument is part of another argument.
--   For example, a decreasing argument in the first element of a pair is not covered.
markOutermostDecreasing :: LIR.Type -> LIR.Type
markOutermostDecreasing (LIR.TypeCon srcSpan name ts _) =
  LIR.TypeCon srcSpan name ts True
markOutermostDecreasing (LIR.FreeTypeCon srcSpan t) =
  LIR.FreeTypeCon srcSpan $ markOutermostDecreasing t
markOutermostDecreasing _ =
  error "Outermost argument is not necessarily unique"
