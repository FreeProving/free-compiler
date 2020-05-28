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

import           Agda.Syntax.Concrete
import           Agda.Syntax.Position
import           Agda.Syntax.Common

import qualified Agda.Syntax.Common            as Agda
import qualified Agda.Syntax.Concrete          as Agda
import qualified Agda.Syntax.Literal           as Agda
import qualified Agda.Syntax.Position          as Agda

-------------------------------------------------------------------------------
-- Identifiers                                                               --
-------------------------------------------------------------------------------

-- | Creates a (not qualified) Agda variable name from a 'String'.
name :: String -> Agda.Name
name ident = Agda.Name Agda.NoRange Agda.InScope [Agda.Id ident]

-- | Create a qualified name given a local variable 'Name' and a list of module
--   'Name's.
qname :: [Agda.Name] -> Agda.Name -> QName
qname ms n = foldr Agda.Qual (Agda.QName n) ms

-- | Creates a qualified name using an empty list of module names.
qname' :: Agda.Name -> Agda.QName
qname' = qname []

-------------------------------------------------------------------------------
-- Imports                                                                   --
-------------------------------------------------------------------------------

-- | Creates an @open import@ declaration for the given qualified name.
--
--   @open import [modName]@
simpleImport :: Agda.QName -> Agda.Declaration
simpleImport modName = Agda.Import
  Agda.NoRange
  modName
  Nothing
  Agda.DoOpen
  (Agda.ImportDirective Agda.NoRange Agda.UseEverything [] [] Nothing)

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Creates an integer literal.
intLiteral :: Integer -> Agda.Expr
intLiteral = Agda.Lit . Agda.LitNat Agda.NoRange

-- | Creates a lambda expression, binding the given names and abstracting the
--   given expression.
--
--   @λ x y … → [expr] @
lambda :: [Agda.Name] -> Agda.Expr -> Agda.Expr
lambda args = Agda.Lam
  Agda.NoRange
  (Agda.DomainFree . Agda.defaultNamedArg . Agda.mkBinder_ <$> args)
