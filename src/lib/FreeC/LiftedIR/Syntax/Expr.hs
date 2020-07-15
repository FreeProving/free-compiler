-- | This module contains the definition of expressions for our lifted
--   intermediate language.

module FreeC.LiftedIR.Syntax.Expr where

import           FreeC.IR.SrcSpan               ( SrcSpan )

import           FreeC.LiftedIR.Effect          ( Effect )
import           FreeC.LiftedIR.Syntax.Name
import           FreeC.LiftedIR.Syntax.Type

-- | An expression.
data Expr
  = -- | A constructor.
    Con { exprSrcSpan :: SrcSpan
        , exprConName :: ConName
        , exprType    :: Type
        }

  | -- | A function or local variable.
    Var { exprSrcSpan :: SrcSpan
        , exprVarName :: VarName
        , exprType    :: Type
        }

  | -- | Function or constructor application.
    App { exprSrcSpan     :: SrcSpan
        , exprAppFunc     :: Expr
        , exprAppTypeArgs :: [Type]   -- ^ Visible type applications.
        , exprEffects     :: [Effect] -- ^ Effect set.
        , exprAppArgs     :: [Expr]   -- ^ Applied arguments.
        , exprType        :: Type
        }

  | -- | @if@ expression.
    If { exprSrcSpan :: SrcSpan
       , ifExprCond  :: Expr
       , ifExprThen  :: Expr
       , ifExprElse  :: Expr
       , exprType    :: Type
       }

  | -- | @case@ expression.
    Case { exprSrcSpan       :: SrcSpan
         , caseExprScrutinee :: Expr
         , caseExprAlts      :: [Alt]
         , exprType          :: Type
         }

  | -- | Error term @undefined@.
    Undefined { exprSrcSpan :: SrcSpan
              , exprType    :: Type
              }

  | -- | Error term @error "<message>"@.
    ErrorExpr { exprSrcSpan  :: SrcSpan
              , errorExprMsg :: String
              , exprType     :: Type
              }

  | -- | An integer literal.
    IntLiteral { exprSrcSpan     :: SrcSpan
               , intLiteralValue :: Integer
               , exprType        :: Type
               }

  | -- | A lambda abstraction.
    Lambda { exprSrcSpan    :: SrcSpan
           , lambdaExprArgs :: [VarPat]
           , lambdaEprRhs   :: Expr
           , exprType       :: Type
           }

  | -- | The @pure@ constructor of the @Free@ monad.
    Pure { exprSrcSpan  :: SrcSpan
         , exprPureArg  :: Expr -- ^ The value that is lifted into the @Free@ monad.
         , exprType     :: Type
         }

  | -- | The bind operator for the free monad.
    Bind { exprSrcSpan  :: SrcSpan
         , exprBindArg  :: Expr -- ^ The left-hand side argument of @>>=@.
         , exprBindCont :: Expr -- ^ The right-hand side argument of @>>=@.
         , exprType     :: Type
         }
 deriving (Eq, Show)

-------------------------------------------------------------------------------
-- Patterns                                                                  --
-------------------------------------------------------------------------------

-- | One alternative of a @case@ expression.
data Alt = Alt
  { altSrcSpan :: SrcSpan
  , altConPat  :: ConPat
  , altVarPats :: [VarPat]
  , altRhs     :: Expr
  }
 deriving (Eq, Show)

-- | A constructor pattern used in an alternative of a @case@ expression.
--
--   The main purpose of this data type is to add location information
--   to a 'ConName'.
data ConPat = ConPat
  { conPatSrcSpan :: SrcSpan
  , conPatName    :: ConName
  }
 deriving (Eq, Show)

-- | A variable pattern used as an argument to a function, lambda abstraction
--   or constructor pattern.
--
--   The variable pattern can optionally have a type signature.
data VarPat = VarPat
  { varPatSrcSpan   :: SrcSpan
  , varPatIdent     :: String
  , varPatType      :: Maybe Type
    -- TODO: remove after EtaConversionPass is moved
  }
 deriving (Eq, Show)
