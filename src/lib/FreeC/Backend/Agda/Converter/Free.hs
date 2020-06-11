-- | This module contains auxilary functions that help to generate Coq code
--   that uses the @Free@ monad.

module FreeC.Backend.Agda.Converter.Free
  ( generatePure
  , free
  , applyFreeArgs
  , addFreeArgs
  )
where

import qualified FreeC.Backend.Agda.Syntax     as Agda
import qualified FreeC.Backend.Agda.Base       as Agda.Base

-- | Applies the @pure@ constructor of the free monad to the given expression.
generatePure :: Agda.Expr -> Agda.Expr
generatePure =
  Agda.app $ Agda.Ident $ Agda.qname [Agda.Base.baseLibName] Agda.Base.pure

-- | Lifts a type in the free monad.
free :: Agda.Expr -> Agda.Expr
free = Agda.app $ applyFreeArgs $ Agda.qname' Agda.Base.free

-- | Apply the @Shape@ and @Pos@ argument to the given type constructor.
--
-- > c ↦ c @S @P
applyFreeArgs :: Agda.QName -> Agda.Expr
applyFreeArgs qname = foldl1
  Agda.app
  [ Agda.Ident qname
  , Agda.Ident (Agda.qname' Agda.Base.shape)
  , Agda.Ident (Agda.qname' Agda.Base.position)
  ]

-- | Adds the resvered names for the free args @Shape@ and @Pos@ to a list of
--   names.
addFreeArgs :: [Agda.Name] -> [Agda.Name]
addFreeArgs ts = Agda.Base.shape : Agda.Base.position : ts