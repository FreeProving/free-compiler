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

import           Compiler.Haskell.SrcSpan
import           Compiler.Pretty

-------------------------------------------------------------------------------
-- Names                                                                     --
-------------------------------------------------------------------------------

-- | An identifier or a symbolic name.
--
--   The constructors of this type do not contain source spans because
--   'Name's are intended to be comparable. They are used as keys to
--   identify nodes of the dependency graph for example.
data Name
  = Ident String     -- ^ An identifier, e.g. @Ident \"f\"@ for a function @f@.
  | Symbol String    -- ^ A symbolic name, e.g. @Symbol \"+\"@ for @(+)@.
 deriving (Eq, Ord, Show)

-- | Extracts an identifier from a Haskell name. Returns @Nothing@ if the
--   given name is a symbol and not an identifier.
identFromName :: Name -> Maybe String
identFromName (Ident  ident) = Just ident
identFromName (Symbol _    ) = Nothing

-- | Haskell identifiers and symbols can be pretty printed because they are
--   often used in error messages.
instance Pretty Name where
  pretty (Ident ident)   = prettyString ident
  pretty (Symbol symbol) = parens (prettyString symbol)

-------------------------------------------------------------------------------
-- Qualified names                                                           --
-------------------------------------------------------------------------------

-- | A potentially qualified 'Name'.
data QName
  = Qual ModName Name -- ^ A qualified 'Name'.
  | UnQual Name       -- ^ An unqualified 'Name'.
 deriving (Eq, Ord, Show)

-- | Extracts an identifier from an unqualified Haskell name.
--
--   Returns @Nothing@ if the given name is qualified or a symbol and not an
--   identifier.
identFromQName :: QName -> Maybe String
identFromQName (UnQual name) = identFromName name
identFromQName (Qual _ _   ) = Nothing

-- | Pretty instance for qualifed Haskell identifiers and symbols.
instance Pretty QName where
  pretty (Qual modid name)
    | null modid = pretty name
    | otherwise = prettyString modid <> dot <> pretty name
  pretty (UnQual name) = pretty name

-------------------------------------------------------------------------------
-- Aliasses for name types                                                   --
-------------------------------------------------------------------------------

-- | The name of a type variable.
type TypeVarIdent = String

-- | The name of a module.
type ModName = String

-- | The name of a function or build-in operator used in prefix notation, e.g.
--   @f x y@ or @(+) n m@
type VarName = QName

-- | The name of an constructor used in prefix notation, e.g. @(:) x xs@.
type ConName = QName

-- | The name of a type or type constructor, e.g. @Integer@ or @[] a@
type TypeConName = QName

-------------------------------------------------------------------------------
-- Internal identifiers                                                      --
-------------------------------------------------------------------------------

-- | The name of a function, data type, type synonym or constructor defined
--   by the user including location information.
--
--   Because the user cannot declare symbols at the moment, the constructor
--   of this data type takes a 'String' and not a 'Name'.
data DeclIdent = DeclIdent
  { declIdentSrcSpan :: SrcSpan
  , fromDeclIdent :: String
  }
 deriving (Eq, Show)

-- | Pretty instance for identifiers in declarations.
instance Pretty DeclIdent where
  pretty = prettyString . fromDeclIdent
  prettyList = prettySeparated (comma <> space) . map pretty

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
  , modPragmas   :: [Pragma]
  , modFuncDecls :: [FuncDecl]
  }
 deriving (Eq, Show)

-- | Pretty instance for modules.
instance Pretty Module where
  pretty ast =
    prettyString "module"
      <+>  prettyString (modName ast)
      <+>  prettyString "where"
      <$$> vcat (map pretty (modImports ast))
      <$$> vcat (map pretty (modTypeDecls ast))
      <$$> vcat (map pretty (modTypeSigs ast))
      <$$> vcat (map pretty (modPragmas ast))
      <$$> vcat (map pretty (modFuncDecls ast))

-------------------------------------------------------------------------------
-- Comments                                                                  --
-------------------------------------------------------------------------------

-- | A comment.
--
--   Comments are collected during parsing. However, the final AST
--   contains no comments. Pragmas (see 'DecArgPragma') are extracted
--   from comments during simplification.
data Comment
  = BlockComment { commentSrcSpan :: SrcSpan, commentText :: String }
    -- ^ A multi-line comment (i.e., @{- ... -}@).
  | LineComment { commentSrcSpan :: SrcSpan, commentText :: String }
    -- ^ A single-line comment (i.e., @-- ...@).

-- | Pretty instance for comments.
instance Pretty Comment where
  pretty (BlockComment _ str) =
    prettyString "{-" <> prettyString str <> prettyString "-}"
  pretty (LineComment _ str) =
    prettyString "--" <> prettyString str

-------------------------------------------------------------------------------
-- Pragmas                                                                   --
-------------------------------------------------------------------------------

-- | All custom pragmas of the compiler start with @HASKELL_TO_COQ@.
customPragmaPrefix :: String
customPragmaPrefix = "HASKELL_TO_COQ"

-- | Data type for custom @{-# HASKELL_TO_COQ ... #-}@ pragmas.
data Pragma
  -- | A @{-# HASKELL_TO_COQ <function> DECREASES ON <argument> #-}@ or
  --   @{-# HASKELL_TO_COQ <function> DECREASES ON ARGUMENT <index> #-}@
  --   pragma.
  = DecArgPragma { pragmaSrcSpan :: SrcSpan
                 , decArgPragmaFuncName :: String
                 , decArgPragmaArg :: (Either String Int)
                 }
 deriving (Eq, Show)

-- | Pretty instance for custom @{-# HASKELL_TO_COQ ... #-}@ pragmas.
instance Pretty Pragma where
  pretty (DecArgPragma _ funcName (Left argName)) = prettyPragma
    (   prettyString funcName
    <+> prettyString "DECREASES ON"
    <+> prettyString argName
    )
  pretty (DecArgPragma _ funcName (Right argIndex)) = prettyPragma
    (   prettyString funcName
    <+> prettyString "DECREASES ON ARGUMENT"
    <+> pretty argIndex
    )

-- | Pretty prints a custom @{-# HASKELL_TO_COQ ... #-}@ pragma with the given
--   contents.
prettyPragma :: Doc -> Doc
prettyPragma contents =
  prettyString "{-#"
    <+> prettyString customPragmaPrefix
    <+> contents
    <+> prettyString "#-}"

-------------------------------------------------------------------------------
-- Imports                                                                   --
-------------------------------------------------------------------------------

-- | An import declaration.
data ImportDecl = ImportDecl
  { importSrcSpan :: SrcSpan
  , importName    :: ModName
  }
 deriving (Eq, Show)

-- | Pretty instance for import declarations.
instance Pretty ImportDecl where
  pretty decl = prettyString "import" <+> prettyString (importName decl)

-------------------------------------------------------------------------------
-- Type arguments                                                            --
-------------------------------------------------------------------------------

-- | The name of a type variable declaration in the head of a data type or
--   type synonym declaration including location information.
type TypeVarDecl = DeclIdent

-- | Converts the declaration of a type variable to a type.
typeVarDeclToType :: TypeVarDecl -> Type
typeVarDeclToType (DeclIdent srcSpan ident) = TypeVar srcSpan ident

-- | Gets the name of the type variable declared by the given type variable
--   declaration.
typeVarDeclName :: TypeVarDecl -> Name
typeVarDeclName = Ident . fromDeclIdent

-- | Gets the unqualified name of the type variable declared by the given
--   type variable declaration.
typeVarDeclQName :: TypeVarDecl -> QName
typeVarDeclQName = UnQual . typeVarDeclName

-------------------------------------------------------------------------------
-- Type declarations                                                         --
-------------------------------------------------------------------------------

-- | A data type or type synonym declaration.
--
--   While it is allowed to define constructors in infix notation, data type
--   and type synonym declarations must not be in infix notation. This is
--   because the @TypeOperators@ language extension is not supported.
data TypeDecl
  = DataDecl
    { typeDeclSrcSpan :: SrcSpan
    , typeDeclIdent :: DeclIdent
    , typeDeclArgs :: [TypeVarDecl]
    , dataDeclCons :: [ConDecl]
    }
  | TypeSynDecl
    { typeDeclSrcSpan :: SrcSpan
    , typeDeclIdent :: DeclIdent
    , typeDeclArgs :: [TypeVarDecl]
    , typeSynDeclRhs :: Type
    }
 deriving (Eq, Show)

-- | Gets the name of the given type declaration.
typeDeclName :: TypeDecl -> Name
typeDeclName = Ident . fromDeclIdent . typeDeclIdent

-- | Gets the unqualified name of the given type declaration.
typeDeclQName :: TypeDecl -> QName
typeDeclQName = UnQual . typeDeclName

-- | Pretty instance for type declarations.
instance Pretty TypeDecl where
  pretty (DataDecl _ declIdent typeVarDecls conDecls) =
    prettyString "data"
      <+> pretty declIdent
      <+> hsep (map pretty typeVarDecls)
      <+> align (vcat (zipWith prettyConDecl [0..] conDecls))
   where
    prettyConDecl :: Int -> ConDecl -> Doc
    prettyConDecl i conDecl | i == 0    = equals <+> pretty conDecl
                            | otherwise = char '|' <+> pretty conDecl
  pretty (TypeSynDecl _ declIdent typeVarDecls typeExpr) =
    prettyString "type"
      <+> pretty declIdent
      <+> hsep (map pretty typeVarDecls)
      <+> equals
      <+> pretty typeExpr

-------------------------------------------------------------------------------
-- Constructor declarations                                                  --
-------------------------------------------------------------------------------

-- | A constructor declaration.
--
--  Even though there is not a dedicated constructor, the constructor is
--  allowed to be in infix notation, but the name of the constructor must
--  not be a symbol.
data ConDecl = ConDecl
  { conDeclSrcSpan :: SrcSpan
  , conDeclIdent :: DeclIdent
  , conDeclFields :: [Type]
  }
 deriving (Eq, Show)

-- | Pretty instance for data constructor declarations.
instance Pretty ConDecl where
  pretty (ConDecl _ declIdent types) =
    pretty declIdent <+> hsep (map pretty types)

-------------------------------------------------------------------------------
-- Type signatures                                                           --
-------------------------------------------------------------------------------

-- | A type signature of one or more function declarations.
data TypeSig = TypeSig
  { typeSigSrcSpan :: SrcSpan
  , typeSigDeclIdents :: [DeclIdent]
  , typeSigTypeSchema :: TypeSchema
  }
 deriving (Eq, Show)

-- | Pretty instance for type signatures.
instance Pretty TypeSig where
  pretty (TypeSig _ declIdents typeSchema) =
    prettySeparated (comma <> space) (map pretty declIdents)
      <+> colon
      <>  colon
      <+> pretty typeSchema

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

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
data FuncDecl = FuncDecl
  { funcDeclSrcSpan    :: SrcSpan
    -- ^ A source span that spans the entire function declaration.
  , funcDeclIdent      :: DeclIdent
    -- ^ The name of the function.
  , funcDeclTypeArgs   :: [TypeVarDecl]
    -- ^ The type arguments of the function.
  , funcDeclArgs       :: [VarPat]
    -- ^ The function's argument patterns.
  , funcDeclRhs        :: Expr
    -- ^ The right-hand side of the function declaration.
  , funcDeclReturnType :: Maybe Type
    -- ^ The return type of the function.
  }
 deriving (Eq, Show)

-- | Gets the name of the given function declaration.
funcDeclName :: FuncDecl -> Name
funcDeclName = Ident . fromDeclIdent . funcDeclIdent

-- | Gets the unqualified name of the given function declaration.
funcDeclQName :: FuncDecl -> QName
funcDeclQName = UnQual . funcDeclName

-- | Gets the type schema of the given function declaration or @Nothing@
--   if at least one of the argument or the return type is not annoated.
funcDeclTypeSchema :: FuncDecl -> Maybe TypeSchema
funcDeclTypeSchema funcDecl = do
  argTypes   <- mapM varPatType (funcDeclArgs funcDecl)
  returnType <- funcDeclReturnType funcDecl
  let typeArgs = funcDeclTypeArgs funcDecl
      typeExpr = funcType NoSrcSpan argTypes returnType
  return (TypeSchema NoSrcSpan typeArgs typeExpr)

-- | Pretty instance for function declarations.
instance Pretty FuncDecl where
  pretty (FuncDecl _ declIdent typeArgs args rhs maybeReturnType) =
    case maybeReturnType of
      Nothing -> prettyFuncHead <+> equals <+> pretty rhs
      Just returnType ->
        prettyFuncHead
          <+> equals
          <+> prettyExprPred 1 rhs
          <+> colon
          <>  colon
          <+> pretty returnType
   where
    -- | The left-hand side of the function declaration.
    prettyFuncHead :: Doc
    prettyFuncHead =
      pretty declIdent
        <+> hsep (map ((char '@' <>) . pretty) typeArgs)
        <+> hsep (map pretty args)

-------------------------------------------------------------------------------
-- Type schemas                                                          --
-------------------------------------------------------------------------------

-- | A Haskell type expression with explicitly introduced type variables.
data TypeSchema = TypeSchema
  { typeSchemaSrcSpan :: SrcSpan
  , typeSchemaArgs :: [TypeVarDecl]
  , typeSchemaType :: Type
  }
 deriving (Eq, Show)

-- | Pretty instance for type schemas.
instance Pretty TypeSchema where
  pretty (TypeSchema _ [] typeExpr) = pretty typeExpr
  pretty (TypeSchema _ typeArgs typeExpr) =
    prettyString "forall"
      <+> hsep (map pretty typeArgs)
      <>  dot
      <+> pretty typeExpr

-------------------------------------------------------------------------------
-- Type expressions                                                          --
-------------------------------------------------------------------------------

-- | A Haskell type expression.
--
--  Build-in types are represented by applications of their type constructors.
--  E.g. the type @[a]@ is represented as
--  @'TypeApp' ('TypeCon' "[]") ('TypeVar' "a")@.
--  The only exception to this rule is the function type @a -> b@. It is
--  represented directly as @'FuncType' ('TypeVar' "a") ('TypeVar' "b")@.
--  The syntax @(->) a b@ is not supported at the moment. This is due to the
--  special role of functions during the translation to Coq.
data Type
  = -- | A type variable.
    TypeVar
      { typeSrcSpan :: SrcSpan
      , typeVarIdent :: TypeVarIdent
      }
  | -- | A type constructor.
    TypeCon
      { typeSrcSpan :: SrcSpan
      , typeConName :: TypeConName
      }
  | -- | A type constructor application.
    TypeApp
      { typeSrcSpan :: SrcSpan
      , typeAppLhs :: Type
      , typeAppRhs :: Type
      }
  | -- | A function type.
    FuncType
      { typeSrcSpan :: SrcSpan
      , funcTypeArg :: Type
      , funcTypeRes :: Type
      }
 deriving (Eq, Show)

-- | Creates a type constructor application type.
--
--   The given source span is inserted into the generated type constructor
--   and every generated type constructor application.
typeApp
  :: SrcSpan     -- ^ The source span to insert into generated nodes.
  -> Type        -- ^ The partially applied type constructor.
  -> [Type]      -- ^ The type arguments to pass to the type constructor.
  -> Type
typeApp srcSpan = foldl (TypeApp srcSpan)

-- | Creates a type constructor application type for the constructor with
--   the given name.
--
--   The given source span is inserted into the generated type constructor
--   and every generated type constructor application.
typeConApp
  :: SrcSpan     -- ^ The source span to insert into generated nodes.
  -> TypeConName -- ^ The name of the type constructor to apply.
  -> [Type]      -- ^ The type arguments to pass to the type constructor.
  -> Type
typeConApp srcSpan = typeApp srcSpan . TypeCon srcSpan

-- | Creates a function type with the given argument and return types.
funcType :: SrcSpan -> [Type] -> Type -> Type
funcType srcSpan = flip (foldr (FuncType srcSpan))

-- | Splits the type of a function or constructor with the given arity
--   into the argument and return types.
--
--   This is basically the inverse of 'funcType'.
splitFuncType :: Type -> Int -> ([Type], Type)
splitFuncType (FuncType _ t1 t2) arity | arity > 0 =
  let (argTypes, returnType) = splitFuncType t2 (arity - 1)
  in  (t1 : argTypes, returnType)
splitFuncType returnType _ = ([], returnType)

-- | Haskell type expressions can be pretty printed because they have to
--   be serialized when the environment is saved to a @.json@ file.
instance Pretty Type where
  pretty = prettyTypePred 0

-- | Pretty prints a type and adds parenthesis if necessary.
--
--   The first argument indicates the precedence of the sourrounding
--   context.
--    * @0@ - Top level. No parenthesis are neccessary.
--    * @1@ - Parenthesis are needed arround function types.
--    * @2@ - Parenthesis are also needed arround type constructor
--            applications.
prettyTypePred :: Int -> Type -> Doc
-- Syntactic sugar for lists.
prettyTypePred _ (TypeApp _ (TypeCon _ name) t) | name == listTypeConName =
  brackets (pretty t)

-- Syntactic sugar for pairs.
-- TODO pretty print arbitrary tuple types.
prettyTypePred _ (TypeApp _ (TypeApp _ (TypeCon _ name) t1) t2)
  | name == tupleTypeConName 2 = parens (pretty t1 <> comma <+> pretty t2)

-- Syntactic sugar for unit.
prettyTypePred _ (TypeCon _ name) | name == unitTypeConName = parens (empty)

-- There are never parentheses around type variables or constructors.
prettyTypePred _ (TypeVar _ ident)                          = prettyString ident
prettyTypePred _ (TypeCon _ name )                          = pretty name

-- There may be parentheses around type appications and function types.
prettyTypePred n (TypeApp _ t1 t2) | n <= 1 =
  prettyTypePred 1 t1 <+> prettyTypePred 2 t2
prettyTypePred 0 (FuncType _ t1 t2) =
  prettyTypePred 1 t1 <+> prettyString "->" <+> pretty t2
prettyTypePred _ t = parens (pretty t)

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
  = -- | A constructor.
    Con { exprSrcSpan :: SrcSpan
        , exprConName :: ConName
        }

  | -- | A function or local variable.
    Var { exprSrcSpan :: SrcSpan
        , exprVarName :: VarName
        }

  | -- | Function or constructor application.
    App { exprSrcSpan :: SrcSpan
        , exprAppLhr :: Expr
        , exprAppRhs :: Expr
        }

  | -- | Visible type application.
    TypeAppExpr { exprSrcSpan :: SrcSpan
                , exprTypeAppLhs :: Expr
                , exprTypeAppRhs :: Type
                }

  | -- | @if@ expression.
    If { exprSrcSpan :: SrcSpan
       , ifExprCond :: Expr
       , ifExprThen :: Expr
       , ifExprElse :: Expr
       }

  | -- | @case@ expression.
    Case { exprSrcSpan :: SrcSpan
         , caseExprScrutinee :: Expr
         , caseExprAlts :: [Alt]
         }

  | -- | Error term @undefined@.
    Undefined { exprSrcSpan :: SrcSpan }

  | -- | Error term @error "<message>"@.
    ErrorExpr { exprSrcSpan :: SrcSpan
              , errorExprMsg :: String
              }

  | -- | An integer literal.
    IntLiteral { exprSrcSpan :: SrcSpan
               , intLiteralValue :: Integer
               }

  | -- | A lambda abstraction.
    Lambda { exprSrcSpan :: SrcSpan
           , lambdaExprArgs :: [VarPat]
           , lambdaEprRhs :: Expr
           }

  | -- | A type annotation.
    ExprTypeSig
      { exprSrcSpan :: SrcSpan
      , exprTypeSigExpr :: Expr
      , exprTypeSigTypeSchema :: TypeSchema
      }
 deriving (Eq, Show)

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

-- | Creates an expression for passing the type arguments of a function or
--   constructor explicitly.
--
--   The given source span is inserted into every generated visible type
--   application node.
visibleTypeApp :: SrcSpan -> Expr -> [Type] -> Expr
visibleTypeApp = foldl . TypeAppExpr

-- | Pretty instance for expressions.
instance Pretty Expr where
  pretty = prettyExprPred 0

-- | Pretty prints an expression and adds parenthesis if necessary.
--
--   The first argument indicates the precedence of the sourrounding
--   context.
--    * @0@ - Top level. No parenthesis are neccessary.
--    * @1@ - Parenthesis are needed around @if@, @case@ and lambda
--            expressions.
--    * @2@ - Parenthesis are also needed around function applications.
prettyExprPred :: Int -> Expr -> Doc

-- Parenthesis can be omitted around @if@, @case@, lambda abstractions
-- and type signatures at top-level only.
prettyExprPred 0 (If _ e1 e2 e3) =
  prettyString "if"
    <+> prettyExprPred 1 e1
    <+> prettyString "then"
    <+> prettyExprPred 0 e2
    <+> prettyString "else"
    <+> prettyExprPred 0 e3
prettyExprPred 0 (Case _ e alts) =
  prettyString "case" <+> prettyExprPred 1 e <+> prettyString "of" <+> braces
    (space <> prettySeparated (semi <> space) (map pretty alts) <> space)
prettyExprPred 0 (Lambda _ args expr) =
  backslash
    <>  hsep (map pretty args)
    <+> prettyString "->"
    <+> prettyExprPred 0 expr
prettyExprPred 0 (ExprTypeSig _ expr typeSchema) =
  prettyExprPred 1 expr <+> colon <> colon <+> pretty typeSchema

-- At all other levels, the parenthesis cannot be omitted.
prettyExprPred _ expr@(If _ _ _ _       ) = parens (pretty expr)
prettyExprPred _ expr@(Case        _ _ _) = parens (pretty expr)
prettyExprPred _ expr@(Lambda      _ _ _) = parens (pretty expr)
prettyExprPred _ expr@(ExprTypeSig _ _ _) = parens (pretty expr)

-- Fix placement of visible type arguments in for error terms.
prettyExprPred n (TypeAppExpr _ (ErrorExpr _ msg) t) | n <= 1 =
  prettyString "error" <+> char '@' <> prettyTypePred 2 t <+> prettyString
    (show msg)

-- Function application is left-associative.
prettyExprPred n expr@(App _ e1 e2)
  | n <= 1    = prettyExprPred 1 e1 <+> prettyExprPred 2 e2
  | otherwise = parens (pretty expr)
prettyExprPred n expr@(TypeAppExpr _ e t)
  | n <= 1    = prettyExprPred 1 e <+> char '@' <> prettyTypePred 2 t
  | otherwise = parens (pretty expr)
prettyExprPred n expr@(ErrorExpr _ msg)
  | n <= 1    = prettyString "error" <+> prettyString (show msg)
  | otherwise = parens (pretty expr)

-- No parenthesis are needed around variable and constructor names and
-- integer literals.
prettyExprPred _ (Con        _ name) = pretty name
prettyExprPred _ (Var        _ name) = pretty name
prettyExprPred _ (IntLiteral _ i   ) = integer i
prettyExprPred _ (Undefined _      ) = prettyString "undefined"

-------------------------------------------------------------------------------
-- @case@ expression alternatives                                            --
-------------------------------------------------------------------------------

-- | One alternative of a case expression.
--
--   Every alternative of a case expression matches a constructor of the
--   matched expression's data type. All arguments of the constructor pattern
--   are variable patterns.
data Alt = Alt
  { altSrcSpan :: SrcSpan
  , altConPat :: ConPat
  , altVarPats :: [VarPat]
  , altRhs :: Expr
  }
 deriving (Eq, Show)

-- | Pretty instance for @case@ expression alternatives.
instance Pretty Alt where
  pretty (Alt _ conPat varPats expr) =
        pretty conPat
    <+> hsep (map pretty varPats)
    <+> prettyString "->"
    <+> pretty expr

-------------------------------------------------------------------------------
-- Constructor patterns                                                      --
-------------------------------------------------------------------------------

-- | A constructor pattern used in an alternative of a @case@ expression.
--
--   The main purpose of this data type is to add location information
--   to a 'ConName'.
data ConPat = ConPat
  { conPatSrcSpan :: SrcSpan
  , conPatName    :: ConName
  }
 deriving (Eq, Show)

-- | Converts a constructor pattern to a constructor expression.
conPatToExpr :: ConPat -> Expr
conPatToExpr (ConPat srcSpan conName) = Con srcSpan conName

-- | Pretty instance for constructor patterns.
instance Pretty ConPat where
  pretty (ConPat _ conName) = pretty conName

-------------------------------------------------------------------------------
-- Variable patterns                                                         --
-------------------------------------------------------------------------------

-- | A variable pattern used as an argument to a function, lambda abstraction
--   or constructor pattern.
--
--   The variable pattern can optionally have a type signature.
data VarPat = VarPat
  { varPatSrcSpan :: SrcSpan
  , varPatIdent   :: String
  , varPatType    :: (Maybe Type)
  }
 deriving (Eq, Show)

-- | Gets the name of the given variable pattern.
varPatName :: VarPat -> Name
varPatName = Ident . varPatIdent

-- | Gets the qualified name of the given variable pattern.
varPatQName :: VarPat -> QName
varPatQName = UnQual . varPatName

-- | Converts a variable pattern to a variable expression.
varPatToExpr :: VarPat -> Expr
varPatToExpr (VarPat srcSpan varName _) = Var srcSpan (UnQual (Ident varName))

-- | Converts the given identifier to a variable pattern without type
--   annotation.
toVarPat :: String -> VarPat
toVarPat ident = VarPat NoSrcSpan ident Nothing

-- | Pretty instance for variable patterns.
instance Pretty VarPat where
  pretty (VarPat _ varName Nothing) = pretty varName
  pretty (VarPat _ varName (Just varType)) =
    parens (pretty varName <+> colon <> colon <+> pretty varType)

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

-- | When inferring the type of 'IntegerLiteral's this is the type to infer.
integerTypeConName :: TypeConName
integerTypeConName = Qual preludeModuleName (Ident "Integer")

-- | When translating @if@ expressions, we annotate the type of the condition
--   with @Bool@.
boolTypeConName :: TypeConName
boolTypeConName = Qual preludeModuleName (Ident "Bool")

-- | The unary prefix operator @-@ is translated to the application of the
--   @negate@ function.
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
