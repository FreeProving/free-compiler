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
  , nextQName
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
  , set
  , dataDecl
  , func
  , pi
  )
where

import           Prelude                 hiding ( pi )

import           Agda.Syntax.Common
import           Agda.Syntax.Concrete
import           Agda.Syntax.Literal
import           Agda.Syntax.Position

import           FreeC.Util.Predicate           ( (.||.) )

-------------------------------------------------------------------------------
-- Identifiers                                                               --
-------------------------------------------------------------------------------

-- | Creates a (not qualified) Agda variable name from a 'String'.
name :: String -> Name
name str = Name NoRange InScope [Id str]

-- | Create a qualified identifier given a local identifier as 'Name' and a
--   list of module 'Name's.
qname :: [Name] -> Name -> QName
qname modules unQName = foldr Qual (QName unQName) modules

-- | Creates a qualified name using an empty list of module names.
qname' :: Name -> QName
qname' = qname []

-- | Creates a new qualified name, by appending a number or incrementing it.
nextQName :: QName -> QName
nextQName (Qual modName qName) = Qual modName $ nextQName qName
nextQName (QName unQName     ) = QName $ nextName unQName

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

-- | Smart constructor for creating a module containing a list of declarations.
moduleDecl :: QName -> [Declaration] -> Declaration
moduleDecl modName = Module NoRange modName []

-- | Smart constructor for creating function type declarations.
--
--   > funcSig foo expr = foo : expr
funcSig :: Name -> Expr -> Declaration
funcSig = TypeSig defaultArgInfo Nothing

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

isApp :: Expr -> Bool
isApp (App _ _ _) = True
isApp _           = False

isFun :: Expr -> Bool
isFun (Fun _ _ _) = True
isFun _           = False
-- | Creates an integer literal.
intLiteral :: Integer -> Expr
intLiteral = Lit . LitNat NoRange

-- | Creates a lambda expression, binding the given names and abstracting the
--   given expression.
--
--   @λ x y … → [expr]@
lambda :: [Name] -> Expr -> Expr
lambda args = Lam NoRange (DomainFree . defaultNamedArg . mkBinder_ <$> args)

-- | Creates an application AST node. Application is left associative and in
--   in type expressions binds stronger than type arrow. For these cases paren-
--   thesis are added automatically.
--
--   > e a
app :: Expr -> Expr -> Expr
app l r =
  App NoRange l $ defaultNamedArg (if isApp .||. isFun $ r then paren r else r)

-- | Wraps the given expression in parenthesis.
paren :: Expr -> Expr
paren = Paren NoRange

-- | Helper function for creating expressions from @String@s.
ident :: String -> Expr
ident = Ident . qname' . name

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------

-- | The first level of Agda's hierarchy of type theoretic universes.
set :: Expr
set = ident "Set"

dataDecl :: Name -> [Declaration] -> Declaration
dataDecl dataName = Data NoRange dataName [] set

-- | A smart constructor for non dependent function types.
func :: Expr -> Expr -> Expr
func l@(Fun _ _ _) = Fun NoRange (defaultArg (paren l)) -- (->) is right assoc.
func l             = Fun NoRange (defaultArg l)

-- | Creates a pi type binding the given names as hidden variables.
--
--   > pi [α, β, γ, …] expr = ∀ {α} {β} {γ} … → expr
pi :: [Name] -> Expr -> Expr
pi decls = Pi [TBind NoRange (bName <$> decls) (Underscore NoRange Nothing)]

-- | Helper function for creating bound, named arguments.
bName :: Name -> NamedArg Binder
bName n = Arg hiddenArgInfo $ Named Nothing $ Binder Nothing $ mkBoundName_ n

-- | Argument meta data marking them as hidden.
hiddenArgInfo :: ArgInfo
hiddenArgInfo = ArgInfo { argInfoHiding        = Hidden
                        , argInfoModality      = defaultModality
                        , argInfoOrigin        = UserWritten
                        , argInfoFreeVariables = UnknownFVs
                        }
