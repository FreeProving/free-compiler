module FreeC.LiftedIR.Converter.Type
  ( convertFuncArgTypes
  , convertConArgType
    -- * Translations
  , convertType
  , convertType'
  )
where

import qualified FreeC.IR.Syntax               as IR
import           FreeC.IR.SrcSpan               ( SrcSpan(NoSrcSpan) )
import qualified FreeC.LiftedIR.Syntax         as LIR

-- | Converts the argument types of a function.
convertFuncArgTypes
  :: Maybe Int -- ^ Index of the decreasing argument for recursive functions.
  -> [IR.Type] -- ^ The argument types.
  -> [LIR.Type]
convertFuncArgTypes = maybe convertNonRecFuncArgTypes convertRecFuncArgTypes

-- | Converts the argument types of a non recursive function using @convertType@.
convertNonRecFuncArgTypes :: [IR.Type] -> [LIR.Type]
convertNonRecFuncArgTypes = map convertType

-- | Converts the argument types of a recursive function using @convertType@.
--
--   The outermost argument at the given index is marked decreasing.
convertRecFuncArgTypes :: Int -> [IR.Type] -> [LIR.Type]
convertRecFuncArgTypes decIndex args =
  let convArgs                      = map convertType args
      (startArgs, decArg : endArgs) = splitAt (decIndex - 1) convArgs
  in  startArgs ++ (markOutermostDecreasing decArg : endArgs)

-- | Converts a constructor argument using @convertType@.
--
--   All occurrences of the constructed type are marked as structurally smaller.
convertConArgType :: IR.QName -> IR.Type -> LIR.Type
convertConArgType ident = markAllDec ident . convertType

-------------------------------------------------------------------------------
-- Translations                                                              --
-------------------------------------------------------------------------------

-- | Converts a type from IR to lifted IR by lifting it into the @Free@ monad.
--
--   This corresponds to the dagger translation for monotypes as described by
--   Abel et al.
--
--   > τ' = Free τ*
convertType :: IR.Type -> LIR.Type
convertType = LIR.FreeTypeCon NoSrcSpan . convertType'

-- | Lifts a type from IR to lifted IR by renaming type variables and
--   constructors, adding the free arguments to constructors and lifting
--   function types in the @Free@ monad.
--
--   This corresponds to the star translation for monotypes as described by
--   Abel et al.
--
--   > (τ₁ τ₂)* = τ₁* τ₂*
--   > (τ₁ -> τ₂)* = τ₁' -> τ₂'
--   > C* = Ĉ Shape Position
--   > α* = α̂
convertType' :: IR.Type -> LIR.Type
convertType' (IR.TypeCon srcSpan name) = LIR.TypeCon srcSpan name [] False
convertType' (IR.TypeVar srcSpan name) = LIR.TypeVar srcSpan name
convertType' (IR.TypeApp _ l r) = convertType' l `LIR.typeApp` convertType' r
convertType' (IR.FuncType srcSpan l r) =
  LIR.FuncType srcSpan (convertType l) (convertType r)

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
  (markAllDec decName `map` ts)
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
