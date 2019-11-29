-- | An alternative AST that represents the subset of Haskell modules that
--   comply with our restrictions on the accepted input format.
--
--   The aim of this module is to make the conversion functions easier to
--   comprehend and reduce coupling with the @haskell-src-ext@ package.
--
--   This AST cannot be parsed directly. Instances of the AST are usually
--   created by converting an existing AST (e.g. from the @haskell-src-ext@
--   package). For testing purposes instances may be created directly.
module Compiler.Haskell.AST where

import           Data.List                      ( intercalate )

import           Compiler.Haskell.SrcSpan
import           Compiler.Pretty

-------------------------------------------------------------------------------
-- Identifiers                                                               --
-------------------------------------------------------------------------------

-- | The name of a type variable.
type TypeVarIdent = String

-- | An identifier or a symbolic name.
--
--   The constructors of this type do not contain source spans because
--   'Name's are intended to be comparable. They are used as keys to
--   identify nodes of the dependency graph for example.
data Name
  = Ident String     -- ^ An identifier, e.g. @Ident \"f\"@ for a function @f@.
  | Symbol String    -- ^ A symbolic name, e.g. @Symbol \"+\"@ for @(+)@.
  deriving (Eq, Ord, Show)

-- | A potentially qualified 'Name'.
data QName
  = Qual ModName Name -- ^ A qualified 'Name'.
  | UnQual Name       -- ^ An unqualified 'Name'.
  deriving (Eq, Ord, Show)

-- | Haskell identifiers and symbols can be pretty printed because they are
--   often used in error messages.
instance Pretty Name where
  pretty (Ident ident)   = prettyString ident
  pretty (Symbol symbol) = parens (prettyString symbol)

-- | Pretty instance for qualifed Haskell identifiers and symbols.
instance Pretty QName where
  pretty (Qual modid name) = prettyString modid <> dot <> pretty name
  pretty (UnQual name) = pretty name

-- | The name of a module.
type ModName = String

-- | The name of a function or build-in operator used in prefix notation, e.g.
--   @f x y@ or @(+) n m@
type VarName = QName

-- | The name of an constructor used in prefix notation, e.g. @(:) x xs@.
type ConName = QName

-- | The name of a type or type constructor, e.g. @Integer@ or @[] a@
type TypeConName = QName

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

-------------------------------------------------------------------------------
-- Internal identifiers                                                      --
-------------------------------------------------------------------------------

-- | The character that is used to mark internal identifiers.
--
--   This is used for example to generate fresh identifiers that don't conflict
--   with actual Haskell identifiers or to hide entries in module interfaces.
internalIdentChar :: Char
internalIdentChar = '@'

-- | Tests whether the given Haskell identifier was generated for internal
--   use only (i.e., contains 'internalIdentChar').
isInternalIdent :: String -> Bool
isInternalIdent ident = elem internalIdentChar ident

-- | Tests whether the given Haskell name was generated for interal use
--   only (i.e., it is an identifier that matches 'isInternalIdent').
isInternalName :: Name -> Bool
isInternalName (Ident  ident) = isInternalIdent ident
isInternalName (Symbol _    ) = False

-- | Tests whether the given qualified Hasell name was generted for internal
--   use only (i.e., the name or module name are internal according to
--   'isInternalIdent' and 'isInternalName', respectively).
isInternalQName :: QName -> Bool
isInternalQName (UnQual name) = isInternalName name
isInternalQName (Qual modIdent name) =
  isInternalIdent modIdent || isInternalName name

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------

-- | A module declaration.
--
--   If the module has no module header, the module name defauts to @'Main'@.
data Module = Module
  { modSrcSpan   :: SrcSpan
  , modName      :: ModName
  , modImports   :: [ImportDecl]
  , modTypeDecls :: [TypeDecl]
  , modTypeSigs  :: [TypeSig]
  , modFuncDecls :: [FuncDecl]
  }
  deriving (Eq, Show)

-------------------------------------------------------------------------------
-- Declarations                                                              --
-------------------------------------------------------------------------------

-- | An import declaration.
data ImportDecl = ImportDecl
  { importSrcSpan :: SrcSpan
  , importName    :: ModName
  }
  deriving (Eq, Show)

-- | A data type or type synonym declaration.
--
--   While it is allowed to define constructors in infix notation, data type
--   and type synonym declarations must not be in infix notation. This is
--   because the @TypeOperators@ language extension is not supported.
data TypeDecl
  = DataDecl SrcSpan DeclIdent [TypeVarDecl] [ConDecl]
  | TypeSynDecl SrcSpan DeclIdent [TypeVarDecl] Type
  deriving (Eq, Show)

-- | A type signature of one or more function declarations.
data TypeSig = TypeSig SrcSpan [DeclIdent] Type
  deriving (Eq, Show)

-- | A function declaration.
--
--   Even though there is not a separate constructor, it is allowed to define
--   functions in infix notation e.g.:
--
--   @
--     append :: [a] -> [a] -> [a]
--     xs \`append\` ys = ...
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
--     infixr 5 \`append\`
--   @
data FuncDecl = FuncDecl SrcSpan DeclIdent [VarPat] Expr
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

-- | Haskell type expressions can be pretty printed because they have to
--   be serialized when the environment is saved to a @.json@ file.
instance Pretty Type where
  pretty = pretty' 0
   where
    -- | Pretty prints a type and adds parenthesis if necessary.
    --
    --   The first argument indicates the precedence of the sourrounding
    --   context.
    --    * @0@ - Top level. No parenthesis are neccessary.
    --    * @1@ - Parenthesis are needed arround function types.
    --    * @2@ - Parenthesis are also needed arround type constructor
    --            applications.
    pretty' :: Int -> Type -> Doc
    -- Syntactic sugar for lists.
    pretty' _ (TypeApp _ (TypeCon _ name) t) | name == listTypeConName =
      brackets (pretty t)

    -- Syntactic sugar for pairs.
    -- TODO pretty print arbitrary tuple types.
    pretty' _ (TypeApp _ (TypeApp _ (TypeCon _ name) t1) t2)
      | name == tupleTypeConName 2 = parens (pretty t1 <> comma <+> pretty t2)

    -- Syntactic sugar for unit.
    pretty' _ (TypeCon _ name)
      | name == unitTypeConName = parens (empty)

    -- There are never parentheses around type variables or constructors.
    pretty' _ (TypeVar _ ident)          = prettyString ident
    pretty' _ (TypeCon _ name )          = pretty name

    -- There may be parentheses around type appications and function types.
    pretty' n (TypeApp _ t1 t2) | n <= 1 = pretty' 1 t1 <+> pretty' 2 t2
    pretty' 0 (TypeFunc _ t1 t2)         = pretty' 1 t1 <+> arrow <+> pretty t2
    pretty' _ t                          = parens (pretty t)

    -- | A document for the function arrow symbol.
    arrow :: Doc
    arrow = prettyString "->"

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | A Haskell expression.
--
--  Even though there are no dedicated constructors, the infix applications of
--  functions and constructors (including left and right sections) are
--  supported. This kind of syntactic sugar is removed during simplification
--  (see "Compiler.Haskell.Simplifier").
data Expr
  = Con SrcSpan ConName           -- ^ A constructor.
  | Var SrcSpan VarName           -- ^ A function or local variable.
  | App SrcSpan Expr Expr         -- ^ Function or constructor application.

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

instance Pretty Expr where
  pretty = pretty' 0
   where
    -- | Pretty prints an expression and adds parenthesis if necessary.
    --
    --   The first argument indicates the precedence of the sourrounding
    --   context.
    --    * @0@ - Top level. No parenthesis are neccessary.
    --    * @1@ - Parenthesis are needed around @if@, @case@ and lambda
    --            expressions.
    --    * @2@ - Parenthesis are also needed around function applications.
    pretty' :: Int -> Expr -> Doc

    -- Parenthesis can be omitted around @if@, @case@ and lambda expressions
    -- at top-level only.
    pretty' 0 (If _ e1 e2 e3) =
          prettyString "if"
      <+> pretty' 1 e1
      <+> prettyString "then"
      <+> pretty' 0 e2
      <+> prettyString "else"
      <+> pretty' 0 e3
    pretty' 0 (Case _ e alts) =
          prettyString "case"
      <+> pretty' 1 e
      <+> prettyString "of"
      <+> braces (space <> prettySeparated semi (map pretty alts) <> space)
    pretty' 0 (Lambda _ args expr) =
      backslash
      <> hsep (map pretty args)
      <+> prettyString "->"
      <+> pretty' 0 expr

    -- Function application is left-associative.
    pretty' n (App _ e1 e2) | n <= 1 = pretty' 1 e1 <+> pretty' 2 e2
    pretty' n (ErrorExpr _ msg) | n <= 1 =
      prettyString "error" <+> prettyString (show msg)

    -- No parenthesis are needed around variable and constructor names and
    -- integer literals.
    pretty' _ (Con _ name) = pretty name
    pretty' _ (Var _ name) = pretty name
    pretty' _ (IntLiteral _ i) = integer i
    pretty' _ (Undefined _) = prettyString "undefined"

    -- Otherwise, there must be parenthesis.
    pretty' _ e = parens (pretty e)

instance Pretty Alt where
  pretty (Alt _ conPat varPats expr) =
        pretty conPat
    <+> hsep (map pretty varPats)
    <+> prettyString "->"
    <+> pretty expr

instance Pretty ConPat where
  pretty (ConPat _ conName) = pretty conName

instance Pretty VarPat where
  pretty (VarPat _ varName) = pretty varName

-------------------------------------------------------------------------------
-- Getters                                                                   --
-------------------------------------------------------------------------------

-- | Extracts the actual identifier from an identifier in a declaration.
fromDeclIdent :: DeclIdent -> String
fromDeclIdent (DeclIdent _ ident) = ident

-- | Extracts the actual identifier from a variable pattern.
fromVarPat :: VarPat -> String
fromVarPat (VarPat _ ident) = ident

-- | Extracts an identifier from a Haskell name. Returns @Nothing@ if the
--   given name is a symbol and not an identifier.
identFromName :: Name -> Maybe String
identFromName (Ident  ident) = Just ident
identFromName (Symbol _    ) = Nothing

-- | Extracts an identifier from an unqualified Haskell name.
--
--   Returns @Nothing@ if the given name is qualified or a symbol and not an
--   identifier.
identFromQName :: QName -> Maybe String
identFromQName (UnQual name) = identFromName name
identFromQName (Qual _ _   ) = Nothing

-- | Splits the type of a function or constructor with the given arity
--   into the argument and return types.
splitType :: Type -> Int -> ([Maybe Type], Maybe Type)
splitType (TypeFunc _ t1 t2) arity | arity > 0 =
  let (argTypes, returnType) = splitType t2 (arity - 1)
  in  (Just t1 : argTypes, returnType)
splitType returnType _ = ([], Just returnType)

-------------------------------------------------------------------------------
-- Declaration identifier getters                                            --
-------------------------------------------------------------------------------

-- | This type class provides a getter for the name of declarations of
--   type @decl@.
class GetDeclIdent decl where
  getDeclIdent :: decl -> DeclIdent

-- | 'GetDeclIdent' instance for data type and type synonym declarations.
instance GetDeclIdent TypeDecl where
  getDeclIdent (DataDecl    _ declIdent _ _) = declIdent
  getDeclIdent (TypeSynDecl _ declIdent _ _) = declIdent

-- | 'GetDeclIdent' instance for function declarations.
instance GetDeclIdent FuncDecl where
  getDeclIdent (FuncDecl _ declIdent _ _) = declIdent

-- | Gets the names of the given declarations and concatenates them with
--   commas.
prettyDeclIdents :: GetDeclIdent decl => [decl] -> String
prettyDeclIdents = intercalate ", " . map fromDeclIdent . map getDeclIdent

-------------------------------------------------------------------------------
-- Source span getters                                                       --
-------------------------------------------------------------------------------

-- | This type class provides a getter for the source span of an AST node of
--   type @a@.
class GetSrcSpan a where
  -- | Gets the source span of the given AST node.
  getSrcSpan :: a -> SrcSpan

-- | 'GetSrcSpan' instance for names of declarations.
instance GetSrcSpan DeclIdent where
  getSrcSpan (DeclIdent srcSpan _) = srcSpan

-- | 'GetSrcSpan' instance for variable patterns.
instance GetSrcSpan VarPat where
  getSrcSpan (VarPat srcSpan _) = srcSpan

-- | 'GetSrcSpan' instance for constructor patterns.
instance GetSrcSpan ConPat where
  getSrcSpan (ConPat srcSpan _) = srcSpan

-- | 'GetSrcSpan' instance for modules.
instance GetSrcSpan Module where
  getSrcSpan = modSrcSpan

-- | 'GetSrcSpan' instance for data type and type synonym declarations.
instance GetSrcSpan TypeDecl where
  getSrcSpan (DataDecl srcSpan _ _ _) = srcSpan
  getSrcSpan (TypeSynDecl srcSpan _ _ _) = srcSpan

instance GetSrcSpan FuncDecl where
  getSrcSpan (FuncDecl srcSpan _ _ _) = srcSpan

instance GetSrcSpan TypeSig where
  getSrcSpan (TypeSig srcSpan _ _  ) = srcSpan

instance GetSrcSpan ImportDecl where
  getSrcSpan (ImportDecl srcSpan _) = srcSpan

-- | 'GetSrcSpan' instance for constructor declarations.
instance GetSrcSpan ConDecl where
  getSrcSpan (ConDecl srcSpan _ _) = srcSpan

-- | 'GetSrcSpan' instance for type expressions.
instance GetSrcSpan Type where
  getSrcSpan (TypeVar  srcSpan _  ) = srcSpan
  getSrcSpan (TypeCon  srcSpan _  ) = srcSpan
  getSrcSpan (TypeApp  srcSpan _ _) = srcSpan
  getSrcSpan (TypeFunc srcSpan _ _) = srcSpan

-- | 'GetSrcSpan' instance for expressions.
instance GetSrcSpan Expr where
  getSrcSpan (Con        srcSpan _    ) = srcSpan
  getSrcSpan (Var        srcSpan _    ) = srcSpan
  getSrcSpan (App        srcSpan _ _  ) = srcSpan
  getSrcSpan (If         srcSpan _ _ _) = srcSpan
  getSrcSpan (Case       srcSpan _ _  ) = srcSpan
  getSrcSpan (Undefined  srcSpan      ) = srcSpan
  getSrcSpan (ErrorExpr  srcSpan _    ) = srcSpan
  getSrcSpan (IntLiteral srcSpan _    ) = srcSpan
  getSrcSpan (Lambda     srcSpan _ _  ) = srcSpan

-- | 'GetSrcSpan' instance for @case@-expression alternatives.
instance GetSrcSpan Alt where
  getSrcSpan (Alt srcSpan _ _ _) = srcSpan

-------------------------------------------------------------------------------
-- Smart constructors                                                        --
-------------------------------------------------------------------------------

-- | Creates a function type with the given argument and return types.
funcType :: SrcSpan -> [Type] -> Type -> Type
funcType srcSpan = flip (foldr (TypeFunc srcSpan))

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
-- Names of predefined modules                                               --
-------------------------------------------------------------------------------

-- | The name of the @Prelude@ module.
--
--   TODO once @import ... as ...@ is supported, the @Prelude@ could be
--        renamed by the user.
preludeModuleName :: ModName
preludeModuleName = "Prelude"

-------------------------------------------------------------------------------
-- Names of predefined type constructors                                     --
-------------------------------------------------------------------------------

-- | The name of the unit type constructor.
unitTypeConName :: TypeConName
unitTypeConName = Qual preludeModuleName (Symbol "")

-- | The name of the @n@-ary tuple type constructor.
tupleTypeConName :: Int -> TypeConName
tupleTypeConName n = Qual preludeModuleName (Symbol (replicate (n - 1) ','))

-- | The name of the list type constructor.
listTypeConName :: TypeConName
listTypeConName = Qual preludeModuleName (Symbol "[]")

-------------------------------------------------------------------------------
-- Names of predefined data constructors                                     --
-------------------------------------------------------------------------------

-- | Name of the unit data constructor.
unitConName :: ConName
unitConName = Qual preludeModuleName (Symbol "")

-- | The name of the empty list data constructor.
nilConName :: ConName
nilConName = Qual preludeModuleName (Symbol "[]")

-- | The name of the non empty list data constructor.
consConName :: ConName
consConName = Qual preludeModuleName (Symbol ":")

-- | The name of the @n@-ary tuple data constructor.
tupleConName :: Int -> ConName
tupleConName n = Qual preludeModuleName (Symbol (replicate (n - 1) ','))

-------------------------------------------------------------------------------
-- Names of special predefined types and operators                           --
-------------------------------------------------------------------------------

-- | When translating @if@ expressions, we annotate the type of the condition
--   with @Bool@. Because we do not support qualified identifiers we
--   need to use this special symbol to prevent the user from shadowing
--   @Bool@ accidentaly with a custom function or local variable.
boolTypeConName :: TypeConName
boolTypeConName = Qual preludeModuleName (Ident "Bool")

-- | When translating boolean expressions in QuickCheck properties, we have to
--   generate a check whether the result is @True@. Because we do not support
--   qualified identifiers we need to use this special symbol to prevent the
--   user from shadowing @True@ accidentaly with a custom constructor.
trueConName :: ConName
trueConName = Qual preludeModuleName (Ident "True")

-- | The unary prefix operator @-@ is translated to the application of the
--   @negate@ function. Because we do not support qualified identifiers we
--   need to use this special symbol to prevent the user from shadowing
--   @negate@ accidentaly with a custom function or local variable.
negateOpName :: VarName
negateOpName = Qual preludeModuleName (Ident "negate")

-------------------------------------------------------------------------------
-- Names of error terms                                                      --
-------------------------------------------------------------------------------

-- | The name of the @error@ function.
errorFuncName :: VarName
errorFuncName = Qual preludeModuleName (Ident "error")

-- | The name of the @undefined@ function.
undefinedFuncName :: VarName
undefinedFuncName = Qual preludeModuleName (Ident "undefined")
