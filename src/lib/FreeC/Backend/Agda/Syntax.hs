-- | This module exports the original Agda AST to reduce coupling with the
--   Agda libraries.

module FreeC.Backend.Agda.Syntax
  ( module Agda.Syntax.Concrete
  , name
  , intLiteral
  , lambda
  )
where

import           Agda.Syntax.Concrete

import qualified Agda.Syntax.Common            as Agda
import qualified Agda.Syntax.Concrete          as Agda
import qualified Agda.Syntax.Literal           as Agda
import qualified Agda.Syntax.Position          as Agda


name :: String -> Agda.Name
name ident = Agda.Name Agda.NoRange Agda.InScope [Agda.Id ident]

intLiteral :: Integer -> Agda.Expr
intLiteral = Agda.Lit . Agda.LitNat Agda.NoRange

lambda :: [Agda.Name] -> Agda.Expr -> Agda.Expr
lambda args = Agda.Lam
  Agda.NoRange
  (Agda.DomainFree . Agda.defaultNamedArg . Agda.mkBinder_ <$> args)
