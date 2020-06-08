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
    -- * Declarations
  , moduleDecl
  , funcSig
    -- * Expressions
  , intLiteral
  , lambda
  , app
  , ident
    -- * Types
  , func
  , pi
  )
where

import           Prelude                 hiding ( pi )

import           Agda.Syntax.Common
import           Agda.Syntax.Concrete
import           Agda.Syntax.Literal
import           Agda.Syntax.Position

hiddenArgInfo :: ArgInfo
hiddenArgInfo = ArgInfo { argInfoHiding        = Hidden
                        , argInfoModality      = defaultModality
                        , argInfoOrigin        = UserWritten
                        , argInfoFreeVariables = UnknownFVs
                        }

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
-- Declarations                                                              --
-------------------------------------------------------------------------------

moduleDecl :: QName -> [Declaration] -> Declaration
moduleDecl modName = Module NoRange modName []

funcSig :: Name -> Expr -> Declaration
funcSig = TypeSig defaultArgInfo Nothing

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Creates an integer literal.
intLiteral :: Integer -> Expr
intLiteral = Lit . LitNat NoRange

-- | Creates a lambda expression, binding the given names and abstracting the
--   given expression.
--
--   @λ x y … → [expr]@
lambda :: [Name] -> Expr -> Expr
lambda args = Lam NoRange (DomainFree . defaultNamedArg . mkBinder_ <$> args)

-- | Creates an application AST node.
--
--   @e a@
app :: Expr -> Expr -> Expr
app l r@(App _ _ _) = App NoRange l $ defaultNamedArg $ paren r -- ($) is left assoc
app l r@(Fun _ _ _) = App NoRange l $ defaultNamedArg $ paren r -- ($) bind stronger than (->)
app l r             = App NoRange l $ defaultNamedArg r

paren :: Expr -> Expr
paren = Paren NoRange

ident :: String -> Expr
ident = Ident . qname' . name

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------

-- | Function type
func :: Expr -> Expr -> Expr
func l@(Fun _ _ _) = Fun NoRange (defaultArg (paren l)) -- (->) is right assoc.
func l             = Fun NoRange (defaultArg l)

pi :: [Name] -> Expr -> Expr
pi decls = Pi [TBind NoRange (bName <$> decls) (Underscore NoRange Nothing)]

bName :: Name -> NamedArg Binder
bName n = Arg hiddenArgInfo $ Named Nothing $ Binder Nothing $ mkBoundName_ n
