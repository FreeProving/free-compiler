-- | This module contains auxilary functions that help to generate Coq code
--   that uses the @Free@ monad.

module FreeC.Backend.Agda.Converter.Free
  ( generatePure
  , free
  , applyFreeArgs
  , addFreeArgs
  , freeDataDecl
  )
where

import           Data.List.Extra                ( snoc )

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
-- > c ↦ c Shape Pos
applyFreeArgs :: Agda.QName -> Agda.Expr
applyFreeArgs qname = foldl1
  Agda.app
  [ Agda.Ident qname
  , Agda.Ident (Agda.qname' Agda.Base.shape)
  , Agda.Ident (Agda.qname' Agda.Base.position)
  ]

-- | Adds the reserved names for the free args @Shape@ and @Pos@ to a list of
--   names.
addFreeArgs :: [Agda.Name] -> [Agda.Name]
addFreeArgs ts = Agda.Base.shape : Agda.Base.position : ts

shape :: Agda.Expr
shape = Agda.Ident $ Agda.qname' $ Agda.Base.shape

-- | Binder for the type arguments of the @Free@ monad.
--
--   > (Shape : Set) (Pos : Shape → Set)
freeArgBinder :: [Agda.LamBinding]
freeArgBinder =
  [ Agda.binding [Agda.Base.shape] Agda.set
  , Agda.binding [Agda.Base.position] (shape `Agda.fun` Agda.set)
  ]

-- | Creates a declaration for a data type, which is parameterized over @Shape@
--   and @Pos@.
freeDataDecl
  :: Agda.Name          -- ^ Name of the data type
  -> [Agda.Name]        -- ^ Names of the bound type variables
  -> [Agda.Declaration] -- ^ List of constructor declarations
  -> Agda.Declaration
freeDataDecl dataName typeNames =
  Agda.dataDecl dataName $ freeArgBinder `snoc` Agda.binding typeNames Agda.set

