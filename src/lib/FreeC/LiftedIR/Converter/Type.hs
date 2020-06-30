module FreeC.LiftedIR.Converter.Type
  ( convertFuncType
  , convertRecFuncType
  , convertConArg
    -- * Translations
  , convertType
  , convertType'
  )
where

import qualified FreeC.IR.Syntax               as IR
import           FreeC.IR.SrcSpan               ( SrcSpan(NoSrcSpan) )
import qualified FreeC.LiftedIR.Syntax         as LIR

-- | Functions not defined in terms of lambdas (@f x = …@ not @f = \x -> …@) aren't
--   evaluated until fully applied, i.e. cannot be bottom. Therefore interleaving
--   monadic layers isn't needed.
--
--   > τ₁ -> … -> τₙ -> ρ ↦ τ₁' -> … -> τₙ' -> ρ'
convertFuncType :: [IR.Type] -> [LIR.Type]
convertFuncType = map convertType

convertRecFuncType :: Int -> [IR.Type] -> [LIR.Type]
convertRecFuncType decIndex args =
  let startArgs = map convertType $ take (decIndex - 1) args
      decArg    = markOutermostDecreasing $ convertType $ args !! decIndex
      endArgs   = map convertType $ drop (decIndex + 1) args
  in  startArgs ++ (decArg : endArgs)

convertConArg :: IR.QName -> IR.Type -> LIR.Type
convertConArg ident = markAllDec ident . convertType

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

-- | Lifts a type from IR to Lifted IR by renaming type variables and
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
