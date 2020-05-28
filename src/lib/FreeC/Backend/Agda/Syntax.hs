-- | This module exports the original Agda AST to reduce coupling with the
--   Agda libraries.

module FreeC.Backend.Agda.Syntax
  ( module Agda.Syntax.Concrete
  , module Agda.Syntax.Common
  , module Agda.Syntax.Position
    -- * Identifiers
  , name
  , qname
  , qname'
    -- * Imports
  , simpleImport
    -- * Expressions
  , intLiteral
  , lambda
  )
where

import           Agda.Syntax.Common
import           Agda.Syntax.Concrete
import           Agda.Syntax.Literal
import           Agda.Syntax.Position

-------------------------------------------------------------------------------
-- Identifiers                                                               --
-------------------------------------------------------------------------------

-- | Creates a (not qualified) Agda variable name from a 'String'.
name :: String -> Name
name ident = Name NoRange InScope [Id ident]

-- | Create a qualified identifier given a local identifier as 'Name' and a
--   list of module 'Name's.
qname :: [Name] -> Name -> QName
qname modules ident = foldr Qual (QName ident) modules

-- | Creates a qualified name using an empty list of module names.
qname' :: Name -> QName
qname' = qname []

-------------------------------------------------------------------------------
-- Imports                                                                   --
-------------------------------------------------------------------------------

-- | Creates an @open import@ declaration for the given qualified name.
--
--   @open import [modName]@
simpleImport :: QName -> Declaration
simpleImport modName = Import
  NoRange
  modName
  Nothing
  DoOpen
  (ImportDirective NoRange UseEverything [] [] Nothing)

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Creates an integer literal.
intLiteral :: Integer -> Expr
intLiteral = Lit . LitNat NoRange

-- | Creates a lambda expression, binding the given names and abstracting the
--   given expression.
--
--   @λ x y … → [expr] @
lambda :: [Name] -> Expr -> Expr
lambda args = Lam NoRange (DomainFree . defaultNamedArg . mkBinder_ <$> args)
