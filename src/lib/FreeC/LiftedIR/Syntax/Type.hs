-- | This module contains the definition of type expressions of our
--   lifted intermediate language.

module FreeC.LiftedIR.Syntax.Type where

import           FreeC.IR.SrcSpan               ( SrcSpan )
import           FreeC.LiftedIR.Syntax.Name

-- | A type expression.
--
--   Types are represented as fully applied type constructors or type variables
--   of kind @*@. In contrast to the 'FreeC.IR.Type' from the intermediate
--   representation, @Free@ is modelled explicitly.
data Type
  = -- | A type variable.
    TypeVar
      { typeSrcSpan  :: SrcSpan
      , typeVarIdent :: TypeVarIdent
      }

  | -- | A fully applied n-ary type constructor application.
    TypeCon
      { typeSrcSpan :: SrcSpan
      , typeConName :: TypeConName
      , typeConArgs :: [Type]
      , typeIsDec   :: Bool
        -- ^ Marks this type as a decreasing element of a type signature.
        --
        --   E.g., recursive constructor arguments or decreasing function
        --   argument. This field is used by the Agda back end to place sized
        --   type annotations.
      }

  | -- | A function type.
    FuncType
      { typeSrcSpan :: SrcSpan
      , funcTypeArg :: Type
      , funcTypeRes :: Type
      }

  | -- | A type constructor for the free monad.
    FreeTypeCon
      { typeSrcSpan :: SrcSpan
      , typeFreeArg :: Type
      }
 deriving (Eq, Show)
