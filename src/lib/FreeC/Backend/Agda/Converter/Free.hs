-- | This module contains auxilary functions that help to generate Coq code
--   that uses the @Free@ monad.
module FreeC.Backend.Agda.Converter.Free
  ( generatePure
  , bind
  , free
  , applyFreeArgs
  , addFreeArgs
  , freeArgBinder
  , undefinedExpr
  , errorExpr
  , addPartial
  ) where

import qualified FreeC.Backend.Agda.Base   as Agda.Base
import qualified FreeC.Backend.Agda.Syntax as Agda

-- | Applies the @pure@ constructor of the free monad to the given expression.
generatePure :: Agda.Expr -> Agda.Expr
generatePure = Agda.app $ Agda.Ident $ Agda.qname [] Agda.Base.pure -- @pure@ is always imported and therefore doesn't need to be qualified.

-- | The infix @>>=@ operator.
bind :: Agda.Expr -> Agda.Expr -> Agda.Expr
bind arg k = Agda.RawApp Agda.NoRange [ arg, Agda.ident ">>=", k ]

-- | Lifts a type in the free monad.
free :: Agda.Expr -> Agda.Expr
free = Agda.app $ applyFreeArgs $ Agda.qname' Agda.Base.free

-- | Apply the @Shape@ and @Pos@ argument to the given type constructor.
--
-- > c ↦ c Shape Pos
applyFreeArgs :: Agda.QName -> Agda.Expr
applyFreeArgs qname = foldl1 Agda.app
  [ Agda.Ident qname
  , Agda.Ident (Agda.qname' Agda.Base.shape)
  , Agda.Ident (Agda.qname' Agda.Base.position)
  ]

-- | Adds the reserved names for the free args @Shape@ and @Pos@ to a list of
--   names.
addFreeArgs :: [ Agda.Name ] -> [ Agda.Name ]
addFreeArgs ts = Agda.Base.shape : Agda.Base.position : ts

-- | Identifier for @Shape@.
--
--   > Shape
shape :: Agda.Expr
shape = Agda.Ident $ Agda.qname' $ Agda.Base.shape

-- | Identifier for @Position@.
--
--   > Position
position :: Agda.Expr
position = Agda.Ident $ Agda.qname' $ Agda.Base.position

-- | Identifier for the partial type class.
partial :: Agda.Expr
partial = Agda.Ident (Agda.qname' Agda.Base.partial)

-- | Binder for the type arguments of the @Free@ monad.
--
--   > (Shape : Set) (Pos : Shape → Set)
freeArgBinder :: [ Agda.LamBinding ]
freeArgBinder
  = [ Agda.binding [ Agda.Base.shape ] Agda.set
    , Agda.binding [ Agda.Base.position ] (shape `Agda.fun` Agda.set)
    ]

-- | The identifier for the error term @undefined@.
undefinedExpr :: Agda.Expr
undefinedExpr = Agda.ident "undefined"

-- | The identifier for the error term @error@.
errorExpr :: Agda.Expr
errorExpr = Agda.ident "error"

-- | Adds an instance argument for the partial type class to the given function
--   type.
--
--   > τ ↦ ⦃ Partial Shape Pos ⦄ → τ
addPartial :: Agda.Expr -> Agda.Expr
addPartial = Agda.fun $ Agda.InstanceArg Agda.NoRange $ Agda.unnamed partial'
 where
   partial' = partial `Agda.app` shape `Agda.app` position
