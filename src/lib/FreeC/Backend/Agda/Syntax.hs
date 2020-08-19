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
  , patternSyn
  , funcDef
    -- * Pattern
  , appP
    -- * Expressions
  , intLiteral
  , stringLiteral
  , lambda
  , app
  , appN
  , ident
  , hiddenArg_
  , ifThenElse
  , caseOf
  , lamClause
    -- * Types
  , set
  , dataDecl
  , binding
  , fun
  , pi
  ) where

import           Prelude              hiding ( pi )

import           Agda.Syntax.Common
import           Agda.Syntax.Concrete
import           Agda.Syntax.Literal
import           Agda.Syntax.Position

import           FreeC.Util.Predicate ( (.||.) )

-------------------------------------------------------------------------------
-- Identifiers                                                               --
-------------------------------------------------------------------------------
-- | Creates a (not qualified) Agda variable name from a 'String'.
name :: String -> Name
name str = Name NoRange InScope $ stringNameParts str

-- | Create a qualified identifier given a local identifier as 'Name' and a
--   list of module 'Name's.
qname :: [Name] -> Name -> QName
qname modules unQName = foldr Qual (QName unQName) modules

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
simpleImport modName = Import NoRange modName Nothing DoOpen
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

-- | Smart constructor for @pattern@ synonyms.
--
--   > pattern C x₁ … xₙ = pure (c x₁ … xₙ)
patternSyn :: Name -> [Arg Name] -> Pattern -> Declaration
patternSyn = PatternSyn NoRange

-- | Smart constructor for function definitions.
--
--   > f a₁ … aₙ = expr
funcDef :: QName -> [QName] -> Expr -> Declaration
funcDef funcName argNames rhs = FunClause lhs' (RHS rhs) NoWhere False
 where
  argPattern = foldl appP (IdentP funcName) $ map IdentP argNames

  lhs'       = LHS argPattern [] [] $ ExpandedEllipsis NoRange 0

-------------------------------------------------------------------------------
-- Pattern                                                                   --
-------------------------------------------------------------------------------
-- | Tests wether the given AST node is an @AppP@.
isAppP :: Pattern -> Bool
isAppP (AppP _ _) = True
isAppP _          = False

-- | Creates an application AST node in a pattern context.
--
--   Application is left associative. Parenthesis are added automatically if
--   the right child is also an @AppP@ node.
--
--   > e a
appP :: Pattern -> Pattern -> Pattern
appP l r = AppP l $ defaultNamedArg $ if isAppP r then ParenP NoRange r else r

-- | Adds parentheses to the pattern iff the root node in the AST is an
--   application.
--
--   On the left-hand side of lambda clauses app patterns have to be
--   parenthesized.
parenIfNeeded :: Pattern -> Pattern
parenIfNeeded p@(AppP _ _) = ParenP NoRange p
parenIfNeeded p = p

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------
-- | Tests whether the given AST node is an @App@.
isApp :: Expr -> Bool
isApp (App _ _ _) = True
isApp (RawApp _ _) = True
isApp _ = False

-- | Tests whether the given AST node is an @Fun@.
isFun :: Expr -> Bool
isFun (Fun _ _ _) = True
isFun _           = False

-- | Creates an integer literal.
intLiteral :: Integer -> Expr
intLiteral = Lit . LitNat NoRange

-- | Creates a string literal.
stringLiteral :: String -> Expr
stringLiteral = Lit . LitString NoRange

-- | Creates a lambda expression, binding the given names and abstracting the
--   given expression.
--
--   @λ x y … → [expr]@
lambda :: [Name] -> Expr -> Expr
lambda args = Lam NoRange (DomainFree . defaultNamedArg . mkBinder_ <$> args)

-- | Creates an application AST node.
--
--   Application is left associative and in type expressions binds stronger
--   than type arrow. For these cases paren- thesis are added automatically.
--
--   > e a
app :: Expr -> Expr -> Expr
app l r = App NoRange l
  $ defaultNamedArg (if isApp .||. isFun $ r then paren r else r)

-- | Applies the list of arguments to the given expression. If the expression is
--   an operator the application is written in mixfix notation.
appN :: Expr -> [Expr] -> Expr
appN f = if isOp f then opApp f else foldl app f

-- | Whether the given expression is an identifier containing an operator (i.e.
--   a name with holes).
isOp :: Expr -> Bool
isOp (Ident n) = isOperator $ unqualify n
isOp _         = False

-- | Applies an operator to a list with the right amount of arguments.
--
--   This functions fails iff the left-hand side isn't an operator or the wrong
--   number of arguments is supplied.
opApp :: Expr -> [Expr] -> Expr
opApp (Ident op)
  = paren . RawApp NoRange . opApp' (nameNameParts $ unqualify $ op)
opApp _          = error "Only an identifier can be an operator!"

-- | Translates a list of @NamePart@s to a list of expressions by replacing
--   holes with arguments and translating name parts to identifiers.
opApp' :: [NamePart] -> [Expr] -> [Expr]
opApp' (Hole : ps) (a : as) = a : opApp' ps as
opApp' (Id part : ps) as = ident part : opApp' ps as
opApp' [] [] = []
opApp' _ _ = error "Wrong number of arguments supplied to operator!"

-- | Wraps the given expression in parenthesis.
paren :: Expr -> Expr
paren = Paren NoRange

-- | Helper function for creating expressions from @String@s.
ident :: String -> Expr
ident = Ident . qname' . name

-- | Hides the given expression.
--
--   > e ↦ {e}
hiddenArg_ :: Expr -> Expr
hiddenArg_ = HiddenArg NoRange . unnamed

-- | @if_then_else_@ from the base library.
--
--   > cond true false ↦ if cond then true else false
ifThenElse :: Expr -> Expr -> Expr -> Expr
ifThenElse cond true false
  = RawApp NoRange [ident "if", cond, ident "then", true, ident "else", false]

-- | @case_of_@ from the base library.
--
--   > disrc clauses ↦ case disrc of λ { clause₁ ; clause₂ ; … }
caseOf :: Expr -> [LamClause] -> Expr
caseOf discr alts
  = RawApp NoRange [ident "case", discr, ident "of", ExtendedLam NoRange alts]

-- | Smart constructor for a clause of a pattern matching lambda abstraction.
--
--   Each @LamClause@ stores a pattern matched on the left-hand side of an @→@
--   and the expression on the right-hand side. In Agda lambda expressions can
--   pattern match on their arguments.
lamClause :: Pattern -> Expr -> LamClause
lamClause pat rhs = LamClause (lhs pat) (RHS rhs) NoWhere False

-- | Smart constructor for a simple 'LHS' for function declarations or lambdas.
lhs :: Pattern -> LHS
lhs pat = LHS (parenIfNeeded pat) [] [] NoEllipsis

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------
-- | The first level of Agda's hierarchy of type theoretic universes.
set :: Expr
set = ident "Set"

-- | Creates a @data@ declaration with the given name, binding the list of type
--   variables and defining the list of constructors.
--
--   > D [b₁, …, bₙ] [C₁, …, Cₘ]
--   >   ↧
--   > data D b₁ … bₙ : Set where
--   >   C₁
--   >   ⋮
--   >   Cₘ
dataDecl :: Name -> [LamBinding] -> Expr -> [Declaration] -> Declaration
dataDecl = Data NoRange

-- | Creates a binder with visible args.
--
--   > [α₁, …, αₙ] e ↦ (α₁ … αₙ : e)
binding :: [Name] -> Expr -> LamBinding
binding types expr = DomainFull $ TBind NoRange (map visibleArg types) expr

-- | Argument meta data marking them as visible.
visibleArg :: Name -> NamedArg Binder
visibleArg = defaultNamedArg . mkBinder_

-- | A smart constructor for non dependent function types.
fun :: Expr -> Expr -> Expr
fun l@(Fun _ _ _) = Fun NoRange (defaultArg (paren l)) -- (->) is right assoc.
fun l = Fun NoRange (defaultArg l)

-- | Creates a pi type binding the given names as hidden variables.
--
--   > pi [α₁, …, αₙ] expr ↦ ∀ {α₁} … {αₙ} → expr
pi :: [Name] -> Expr -> Expr
pi decls expr
  | (Pi binders expr') <- expr = Pi (binder : binders) expr'
  | otherwise = Pi [binder] expr
 where
  binder = TBind NoRange (map hiddenArg decls) $ Underscore NoRange Nothing

-- | Helper function for creating hidden named arguments.
hiddenArg :: Name -> NamedArg Binder
hiddenArg n
  = Arg hiddenArgInfo $ Named Nothing $ Binder Nothing $ mkBoundName_ n

-- | Argument meta data marking them as hidden.
hiddenArgInfo :: ArgInfo
hiddenArgInfo = ArgInfo
  { argInfoHiding        = Hidden
  , argInfoModality      = defaultModality
  , argInfoOrigin        = UserWritten
  , argInfoFreeVariables = UnknownFVs
  }
