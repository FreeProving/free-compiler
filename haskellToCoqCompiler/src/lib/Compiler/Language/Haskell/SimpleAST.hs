-- | An alternative AST that represents the subset of Haskell modules that
--   comply with our restrictions on the accepted input format.
--
--   The aim of this module is to make the conversion functions easier to
--   comprehend and reduce coupling with the @haskell-src-ext@ package.
--
--   This AST can neither be parsed nor pretty printed directly. Instances of
--   the AST are usually created by converting an existing AST (e.g. from the
--   @haskell-src-ext@ package). For testing purposes instances may be created
--   directly.
module Compiler.Language.Haskell.SimpleAST where

import           Compiler.Pretty
import           Compiler.SrcSpan

-------------------------------------------------------------------------------
-- Identifiers                                                               --
-------------------------------------------------------------------------------

-- | The name of a module including the dots.
type ModuleIdent = String

-- | The name of a type variable.
type TypeVarIdent = String

-- | An identifier or a symbolic name.
--
--   The constructors of this type do not contain source spans because
--   'Name's are intended to be comparable. They are used as keys to
--   identify nodes of the dependency graph for example.
data Name
  = Ident String  -- ^ An identifier, e.g. @Ident "f"@ for a function @f@.
  | Symbol String -- ^ A symbolic name, e.g. @Symbol "+"@ for @(+)@.
  deriving (Eq, Ord, Show)

-- | Haskell identifiers and symbols can be pretty printed because they are
--   often used in error messages.
instance Pretty Name where
  pretty (Ident ident) = prettyString ident
  pretty (Symbol symbol) = parens (prettyString symbol)

-- | The name of a function, constructor or build-in operator used in infix
--   notation, e.g. @x `f` y@ or @x : xs@, @n + m@.
type OpName = Name

-- | The name of a function or build-in operator used in prefix notation, e.g.
--   @f x y@ or @(+) n m@
type VarName = Name

-- | The name of an constructor used in prefix notation, e.g. @(:) x xs@.
type ConName = Name

-- | The name of a type or type constructor, e.g. @Int@ or @[] a@
type TypeConName = Name

-- | The name of a function, data type, type synonym or constructor defined
--   by the user including location information.
--
--   Because the user cannot declare symbols at the moment, the constructor
--   of this data type takes a 'String' and not a 'Name'.
data DeclIdent = DeclIdent SrcSpan String
  deriving (Eq, Show)

-- | The name of a type variable declaration in the head of a data type or
--   type synonym declaration including location information.
type TypeVarDecl = DeclIdent

-- | A constructor pattern used in an alternative of a @case@ expression.
--
--   The only purpose of this data type is to add location information
--   to a 'ConName'.
data ConPat = ConPat SrcSpan ConName
  deriving (Eq, Show)

-- | A variable pattern used as an argument to a function, lambda abstraction
--   or constructor pattern.
--
--   The only purpose of this data type is to add location information to
--   the identifer for a variable.
data VarPat = VarPat SrcSpan String
  deriving (Eq, Show)

-- | The name of a function or constructor that is used in infix notation.
--
--   E.g. @'VarOp' ('Ident' "f")@ for @`f`@ or @'ConOp' ('Symbol' ":")@
--   for @(:)@.
data Op = VarOp SrcSpan OpName | ConOp SrcSpan OpName
  deriving (Eq, Show)

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------

-- | A module declaration.
--
--   If the module has no module header, the module name is @'Nothing'@.
data Module = Module
  SrcSpan             -- ^ A source span that spans the entire module.
  (Maybe ModuleIdent) -- ^ Optional name of the module.
  [Decl]              -- ^ The declarations.
  deriving (Eq, Show)

-------------------------------------------------------------------------------
-- Declarations                                                              --
-------------------------------------------------------------------------------

-- | A Haskell declaration.
--
--   Even though there is not a separate constructor, it is allowed to define
--   functions in infix notation e.g.:
--
--   @
--     append :: [a] -> [a] -> [a]
--     xs `append` ys = ...
--   @
--
--   But it is currently not supported to use symbolic names for such
--   definitions. Thus the following is not allowed:
--
--   @
--     (++) :: [a] -> [a] -> [a]
--     xs ++ ys = ...
--   @
--
--   The precedence and associativity (fixity) of infix declarations can be
--   specified as well.
--
--   @
--     infixr 5 `append`
--   @
--
--   While it is allowed to define constructors in infix notation, data type
--   and type synonym declarations must not be in infix notation. This is
--   because the @TypeOperators@ language extension is not supported.
data Decl
  = DataDecl SrcSpan DeclIdent [TypeVarDecl] [ConDecl]
    -- ^ A data type declaration.
  | TypeDecl SrcSpan DeclIdent [TypeVarDecl] Type
    -- ^ A type synonym declaration.
  | FuncDecl SrcSpan DeclIdent [VarPat] Expr
    -- ^ A function declaration.
  | TypeSig SrcSpan [DeclIdent] Type
    -- ^ A type signature of one or more function declarations.
  | FixitySig SrcSpan Assoc (Maybe Int) [Op]
    -- ^ A fixity signature of an infix declaration.
  deriving (Eq, Show)

-- | A constructor declaration.
--
--  Even though there is not a dedicated constructor, the constructor is
--  allowed to be in infix notation, but the name of the constructor must
--  not be a symbol.
data ConDecl = ConDecl
  SrcSpan   -- ^ A source span that spans the entire constructor declaration.
  DeclIdent -- ^ The name of the constructor.
  [Type]    -- ^ The types of the constructor arguments.
  deriving (Eq, Show)

-- | The associativity of a infix declaration.
data Assoc = AssocNone | AssocLeft | AssocRight
  deriving (Eq, Show)

-------------------------------------------------------------------------------
-- Type expressions                                                          --
-------------------------------------------------------------------------------

-- | A Haskell type expression.
--
--  Build-in types are represented by applications of their type constructors.
--  E.g. the type @[a]@ is represented as
--  @'TypeApp' ('TypeCon' "[]") ('TypeVar' "a")@.
--  The only exception to this rule is the function type @a -> b@. It is
--  represented directly as @'TypeFunc' ('TypeVar' "a") ('TypeVar' "b")@.
--  The syntax @(->) a b@ is not supported at the moment. This is due to the
--  special role of functions during the translation to Coq.
data Type
  = TypeVar SrcSpan TypeVarIdent -- ^ A type variable.
  | TypeCon SrcSpan TypeConName  -- ^ A type constructor.
  | TypeApp SrcSpan Type Type    -- ^ A type constructor application.
  | TypeFunc SrcSpan Type Type   -- ^ A function type.
  deriving (Eq, Show)

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | A Haskell expression.
data Expr
  = Con SrcSpan ConName           -- ^ A constructor.
  | Var SrcSpan VarName           -- ^ A function or local variable.

  | App SrcSpan Expr Expr         -- ^ Function or constructor application.

  | InfixApp SrcSpan Expr Op Expr -- ^ Infix application of a function or constructor.
  | LeftSection SrcSpan Expr Op   -- ^ Partial infix application with left argument.
  | RightSection SrcSpan Op Expr  -- ^ Partial infix application with right argument.
  | NegApp SrcSpan Expr           -- ^ Application of the negation prefix operator.

  | If SrcSpan Expr Expr Expr     -- ^ @if@ expression.
  | Case SrcSpan Expr [Alt]       -- ^ @case@ expression.

  | Undefined SrcSpan             -- ^ Error term @undefined@.
  | ErrorExpr SrcSpan String      -- ^ Error term @error "<message>"@.

  | IntLiteral SrcSpan Integer    -- ^ An integer literal.
  | Lambda SrcSpan [VarPat] Expr  -- ^ A lambda abstraction.
  deriving (Eq, Show)

-- | One alternative of a case expression.
--
--   Every alternative of a case expression matches a constructor of the
--   matched expression's data type. All arguments of the constructor pattern
--   are variable patterns.
data Alt = Alt
  SrcSpan      -- ^ A source span that spans the entire alternative.
  ConPat       -- ^ The name of the constructor matched by this alternative.
  [VarPat]     -- ^ Variable patterns for the arguments of the constructor.
  Expr         -- ^ The right hand side of this alternative.
  deriving (Eq, Show)

-------------------------------------------------------------------------------
-- Smart constructors                                                        --
-------------------------------------------------------------------------------

-- | Creates a type constructor application type.
--
--   The given source span is inserted into the generated type constructor
--   and every generated type constructor application.
typeApp
  :: SrcSpan     -- ^ The source span to insert into generated nodes.
  -> TypeConName -- ^ The name of the type constructor to apply.
  -> [Type]      -- ^ The type arguments to pass to the type constructor.
  -> Type
typeApp srcSpan = foldl (TypeApp srcSpan) . TypeCon srcSpan

-- | Creates an expression for applying the given expression to the provided
--   arguments.
--
--   The given source span is inserted into the generated function application
--   expressions.
app :: SrcSpan -> Expr -> [Expr] -> Expr
app = foldl . App

-- | Creates an expression for applying the function with the given name.
--
--   The given source span is inserted into the generated function reference
--   and every generated function application.
varApp
  :: SrcSpan -- ^ The source span to insert into generated nodes.
  -> VarName -- ^ The name of the function to apply.
  -> [Expr]  -- ^ The arguments to pass to the function.
  -> Expr
varApp srcSpan = app srcSpan . Var srcSpan

-- | Creates a data constructor application expression.
--
--   The given source span is inserted into the generated constructor reference
--   and every generated constructor application.
conApp
  :: SrcSpan -- ^ The source span to insert into generated nodes.
  -> ConName -- ^ The name of the constructor to apply.
  -> [Expr]  -- ^ The arguments to pass to the constructor.
  -> Expr
conApp srcSpan = app srcSpan . Con srcSpan

-------------------------------------------------------------------------------
-- Names of predefined type constructors                                     --
-------------------------------------------------------------------------------

-- | The name of the unit type constructor.
unitTypeConName :: TypeConName
unitTypeConName = Symbol "()"

-- | The name of the pair type constructor.
pairTypeConName :: TypeConName
pairTypeConName = Symbol "(,)"

-- | The name of the list type constructor.
listTypeConName :: TypeConName
listTypeConName = Symbol "[]"

-------------------------------------------------------------------------------
-- Names of predefined data constructors                                     --
-------------------------------------------------------------------------------

-- | Name of the unit data constructor.
unitConName :: ConName
unitConName = Symbol "()"

-- | The name of the empty list data constructor.
nilConName :: ConName
nilConName = Symbol "[]"

-- | The name of the non empty list data constructor.
consConName :: ConName
consConName = Symbol ":"

-- | The name of the pair data constructor.
pairConName :: ConName
pairConName = Symbol "(,)"
