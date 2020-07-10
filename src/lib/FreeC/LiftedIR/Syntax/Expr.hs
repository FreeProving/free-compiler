-- | This module contains the definition of expressions for our lifted
--   intermediate language.

module FreeC.LiftedIR.Syntax.Expr where

import           FreeC.IR.SrcSpan               ( SrcSpan )

import           FreeC.LiftedIR.Effect          ( Effect )
import           FreeC.LiftedIR.Syntax.Name
import           FreeC.LiftedIR.Syntax.Type

import qualified FreeC.Backend.Agda.Syntax     as Agda

-- | An expression.
data Expr
  = -- | A constructor.
    Con { exprSrcSpan :: SrcSpan
        , exprConName :: ConName
        }

  | -- | A smart constructor.
    SmartCon { exprSrcSpan :: SrcSpan
             , exprConName :: ConName
             }

  | -- | A function or local variable.
    Var { exprSrcSpan     :: SrcSpan
        , exprVarName     :: VarName
        , exprAgdaVarName :: Agda.QName
        }

  | -- | Function or constructor application.
    App { exprSrcSpan     :: SrcSpan
        , exprAppFunc     :: Expr
        , exprAppTypeArgs :: [Type]   -- ^ Visible type applications.
        , exprEffects     :: [Effect] -- ^ Effect set.
        , exprAppArgs     :: [Expr]   -- ^ Applied arguments.
        }

  | -- | @if@ expression.
    If { exprSrcSpan :: SrcSpan
       , ifExprCond  :: Expr
       , ifExprThen  :: Expr
       , ifExprElse  :: Expr
       }

  | -- | @case@ expression.
    Case { exprSrcSpan       :: SrcSpan
         , caseExprScrutinee :: Expr
         , caseExprAlts      :: [Alt]
         }

  | -- | Error term @undefined@.
    Undefined { exprSrcSpan :: SrcSpan
              }

  | -- | Error term @error "<message>"@.
    ErrorExpr { exprSrcSpan  :: SrcSpan
              , errorExprMsg :: String
              }

  | -- | An integer literal.
    IntLiteral { exprSrcSpan     :: SrcSpan
               , intLiteralValue :: Integer
               }

  | -- | A lambda abstraction.
    Lambda { exprSrcSpan    :: SrcSpan
           , lambdaExprArgs :: [VarPat]
           , lambdaExprRhs  :: Expr
           }

  | -- | The @pure@ constructor of the @Free@ monad.
    Pure { exprSrcSpan  :: SrcSpan
         , exprPureArg  :: Expr -- ^ The value that is lifted into the @Free@ monad.
         }

  | -- | The bind operator for the free monad.
    Bind { exprSrcSpan  :: SrcSpan
         , exprBindArg  :: Expr -- ^ The left-hand side argument of @>>=@.
         , exprBindCont :: Expr -- ^ The right-hand side argument of @>>=@.
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
    -- TODO: remove maybe after EtaConversionPass is moved
  , varPatAgdaIdent :: Agda.QName
  }
 deriving (Eq, Show)
