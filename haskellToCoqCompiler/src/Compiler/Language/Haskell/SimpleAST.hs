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

-- | The name of a module including the dots.
type ModuleIdent = String

-- | The name of a function, data type, type synonym or constructor defined
--   by the user.
--
--   This type is used in the constructors of 'Decl' to indicate that
--   symbols cannot be used in declarations.
type DeclIdent = String

-- | The name of a type variable.
type TypeVarIdent = String

-- | The name of a variable pattern.
--
--   This type is used for function arguments and the arguments of constructor
--   patterns in @case@ expressions.
type VarIdent = String

-- | An identifier or a symbolic name.
data Name
  = Ident String  -- ^ An identifier, e.g. @Ident "f"@ for a function @f@.
  | Symbol String -- ^ A symbolic name, e.g. @Symbol "+"@ for @(+)@.

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

-- | A module declaration.
--
--   If the module has no module header, the module name is @'Nothing'@.
data Module = Module
  (Maybe ModuleIdent) -- ^ Optional name of the module.
  [Decl]              -- ^ The declarations.

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
  = DataDecl DeclIdent [TypeVarIdent] [ConDecl]
    -- ^ A data type declaration.
  | TypeDecl DeclIdent [TypeVarIdent] Type
    -- ^ A type synonym declaration.
  | FuncDecl DeclIdent [VarIdent] Expr
    -- ^ A function declaration.
  | TypeSig   [DeclIdent] Type
    -- ^ A type signature of one or more function declarations.
  | FixitySig Assoc (Maybe Int) [Op]
    -- ^ A fixity signature of an infix declaration.

-- | A constructor declaration.
--
--  Even though there is not a dedicated constructor, the constructor is
--  allowed to be in infix notation, but the name of the constructor must
--  not be a symbol.
data ConDecl = ConDecl
  DeclIdent -- ^ The name of the constructor.
  [Type]    -- ^ The types of the constructor arguments.

-- | The associativity of a infix declaration.
data Assoc = AssocNone | AssocLeft | AssocRight

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
  = TypeVar TypeVarIdent -- ^ A type variable.
  | TypeCon TypeConName  -- ^ A type constructor.
  | TypeApp Type Type    -- ^ A type constructor application.
  | TypeFunc Type Type   -- ^ A function type.

-- | A Haskell expression.
data Expr
  = Con ConName            -- ^ A constructor.
  | Var  VarName           -- ^ A function or local variable.

  | App Expr Expr          -- ^ Function or constructor application.

  | InfixApp Expr Op Expr  -- ^ Infix application of a function or constructor.
  | LeftSection Expr Op    -- ^ Partial infix application with left argument.
  | RightSection Op Expr   -- ^ Partial infix application with right argument.
  | NegApp Expr            -- ^ Application of the negation prefix operator.

  | If Expr Expr Expr      -- ^ @if@ expression.
  | Case Expr [Alt]        -- ^ @case@ expression.

  | Undefined              -- ^ Error term @undefined@.
  | ErrorExpr String       -- ^ Error term @error "<message>"@.

  | IntLiteral Integer     -- ^ An integer literal.
  | Lambda [VarIdent] Expr -- ^ A lambda abstraction.

-- | The name of a function or constructor that is used in infix notation.
--
--   E.g. @'VarOp' ('Ident' "f")@ for @`f`@ or @'ConOp' ('Symbol' ":")@
--   for @(:)@.
data Op = VarOp OpName | ConOp OpName

-- | One alternative of a case expression.
--
--   Every alternative of a case expression matches a constructor of the
--   matched expression's data type. All arguments of the constructor pattern
--   are variable patterns.
data Alt = Alt
  ConName    -- ^ The name of the constructor matched by this alternative.
  [VarIdent] -- ^ Variable patterns for the arguments of the constructor.
  Expr       -- ^ The right hand side of this alternative.

-- | Creates a type constructor application type.
typeApp
  :: TypeConName -- ^ The name of the type constructor to apply.
  -> [Type]      -- ^ The type arguments to pass to the type constructor.
  -> Type
typeApp = foldl TypeApp . TypeCon

-- | The name of the unit type constructor.
unitTypeConName :: TypeConName
unitTypeConName = Symbol "()"

-- | The name of the pair type constructor.
pairTypeConName :: TypeConName
pairTypeConName = Symbol "(,)"

-- | The name of the list type constructor.
listTypeConName :: TypeConName
listTypeConName = Symbol "[]"

-- | Creates an expression for applying the function with the given name.
varApp
  :: VarName -- ^ The name of the function to apply.
  -> [Expr]  -- ^ The arguments to pass to the function.
  -> Expr
varApp = foldl App . Var

-- | Creates a data constructor application expression.
conApp
  :: ConName -- ^ The name of the constructor to apply.
  -> [Expr]  -- ^ The arguments to pass to the constructor.
  -> Expr
conApp = foldl App . Con

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
