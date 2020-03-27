-- | This module contains the abstract syntax tree (AST) for the intermediate
--   representation (IR) of the compiler.
--
--   The intermediate language is very similar to the subset of Haskell
--   supported by the compiler. The main goal is to make the transformations
--   on the AST and code generation functions easier to comprehend. The IR does
--   have fewer syntactic constructs than  Haskell AST that fewer cases need to
--   be distinguished. For example, there is no explicit representation of
--   infix function applications and no list literals. These kinds of syntactic
--   sugar must be removed by the front end.
--
--   An additional goal of this AST is to reduce coupling with the parsing
--   library and source language. Ideally the compiler works with any language
--   whose AST can be transformed into this intermediate representation.
--
--   At the moment there is no parser for this AST. Instances of the AST are
---  usually created by converting an existing AST (e.g. a Haskell AST from
--   the @haskell-src-ext@ package). However, the AST can be pretty printed.
--   It's syntax is based on Haskell's syntax.
module Compiler.IR.Syntax where

import           Control.Monad                  ( (>=>) )

import           Compiler.IR.SrcSpan
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

-- | Extracts an identifier from a name. Returns @Nothing@ if the
--   given name is a symbol and not an identifier.
identFromName :: Name -> Maybe String
identFromName (Ident  ident) = Just ident
identFromName (Symbol _    ) = Nothing

-- | Pretty instance for identifiers and symbols.
instance Pretty Name where
  pretty (Ident  ident ) = prettyString ident
  pretty (Symbol symbol) = parens (prettyString symbol)
  prettyList = prettySeparated (comma <> space) . map pretty

-------------------------------------------------------------------------------
-- Qualified names                                                           --
-------------------------------------------------------------------------------

-- | A qualifiable 'Name'.
data QName
  = Qual ModName Name -- ^ A qualified 'Name'.
  | UnQual Name       -- ^ An unqualified 'Name'.
 deriving (Eq, Ord, Show)

-- | Extracts the name of a qualifiable name.
nameFromQName :: QName -> Name
nameFromQName (UnQual name) = name
nameFromQName (Qual _ name) = name

-- | Extracts an identifier from a qualifiable name.
identFromQName :: QName -> Maybe String
identFromQName = identFromName . nameFromQName

-- | Converts a qualifiable name to a name that is qualified with
--   the given module name.
toQual :: ModName -> QName -> QName
toQual modName' = Qual modName' . nameFromQName

-- | Converts a qualifiable name to an unqualified name.
toUnQual :: QName -> QName
toUnQual = UnQual . nameFromQName

-- | Pretty instance for qualifiable identifiers and symbols.
instance Pretty QName where
  pretty (Qual modid name)
    | null modid = pretty name
    | otherwise  = prettyString modid <> dot <> pretty name
  pretty (UnQual name) = pretty name
  prettyList = prettySeparated (comma <> space) . map pretty

-------------------------------------------------------------------------------
-- Aliases for name types                                                    --
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
-- Names of top-level declarations                                           --
-------------------------------------------------------------------------------

-- | The name of a top-level declaration including location information.
data DeclIdent = DeclIdent
  { declIdentSrcSpan :: SrcSpan
  , declIdentName    :: QName
  }
 deriving (Eq, Show)

-- | Pretty instance for names of declarations.
instance Pretty DeclIdent where
  pretty     = pretty . declIdentName
  prettyList = prettySeparated (comma <> space) . map pretty

-------------------------------------------------------------------------------
-- Internal identifiers                                                      --
-------------------------------------------------------------------------------

-- | The character that is used to mark internal identifiers.
--
--   This is used to generate fresh identifiers that don't conflict with user
--   defined identifiers.
internalIdentChar :: Char
internalIdentChar = '@'

-- | Tests whether the given identifier was generated for internal use only
--   (i.e., contains 'internalIdentChar').
isInternalIdent :: String -> Bool
isInternalIdent ident = elem internalIdentChar ident

-- | Tests whether the given name was generated for internal use only (i.e.,
--   it is an identifier that matches 'isInternalIdent').
isInternalName :: Name -> Bool
isInternalName (Ident  ident) = isInternalIdent ident
isInternalName (Symbol _    ) = False

-- | Tests whether the given qualifiable name was generated for internal use
--   only (i.e., the qualified name is internal according to 'isInternalName').
isInternalQName :: QName -> Bool
isInternalQName (UnQual name) = isInternalName name
isInternalQName (Qual _ name) = isInternalName name

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------

-- | A module declaration.
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
--   from comments by the front end.
data Comment
  = BlockComment { commentSrcSpan :: SrcSpan, commentText :: String }
    -- ^ A multi-line comment (i.e., @{- ... -}@).
  | LineComment { commentSrcSpan :: SrcSpan, commentText :: String }
    -- ^ A single-line comment (i.e., @-- ...@).

-- | Pretty instance for comments.
instance Pretty Comment where
  pretty (BlockComment _ str) =
    prettyString "{-" <> prettyString str <> prettyString "-}"
  pretty (LineComment _ str) = prettyString "--" <> prettyString str

-------------------------------------------------------------------------------
-- Pragmas                                                                   --
-------------------------------------------------------------------------------

-- | All custom pragmas of the compiler start with @HASKELL_TO_COQ@.
customPragmaPrefix :: String
customPragmaPrefix = "HASKELL_TO_COQ"

-- | Data type for custom @{-\# HASKELL_TO_COQ ... \#-}@ pragmas.
data Pragma
  -- | A @{-\# HASKELL_TO_COQ <function> DECREASES ON <argument> \#-}@ or
  --   @{-\# HASKELL_TO_COQ <function> DECREASES ON ARGUMENT <index> \#-}@
  --   pragma.
  = DecArgPragma { pragmaSrcSpan :: SrcSpan
                 , decArgPragmaFuncName :: QName
                 , decArgPragmaArg :: (Either String Int)
                 }
 deriving (Eq, Show)

-- | Pretty instance for custom @{-\# HASKELL_TO_COQ ... \#-}@ pragmas.
instance Pretty Pragma where
  pretty (DecArgPragma _ funcName (Left argName)) = prettyPragma
    (pretty funcName <+> prettyString "DECREASES ON" <+> prettyString argName)
  pretty (DecArgPragma _ funcName (Right argIndex)) = prettyPragma
    (   pretty funcName
    <+> prettyString "DECREASES ON ARGUMENT"
    <+> pretty argIndex
    )

-- | Pretty prints a custom @{-\# HASKELL_TO_COQ ... \#-}@ pragma with the given
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
data TypeVarDecl = TypeVarDecl
  { typeVarDeclSrcSpan :: SrcSpan
  , typeVarDeclIdent   :: String
  }
 deriving (Eq, Show)

-- | Converts the declaration of a type variable to a type.
typeVarDeclToType :: TypeVarDecl -> Type
typeVarDeclToType (TypeVarDecl srcSpan ident) = TypeVar srcSpan ident

-- | Gets the name of the type variable declared by the given type variable
--   declaration.
typeVarDeclName :: TypeVarDecl -> Name
typeVarDeclName = Ident . typeVarDeclIdent

-- | Gets the unqualified name of the type variable declared by the given
--   type variable declaration.
typeVarDeclQName :: TypeVarDecl -> QName
typeVarDeclQName = UnQual . typeVarDeclName

-- | Pretty instance for type variable declaration.
instance Pretty TypeVarDecl where
  pretty = pretty . typeVarDeclIdent

-------------------------------------------------------------------------------
-- Type declarations                                                         --
-------------------------------------------------------------------------------

-- | A data type or type synonym declaration.
data TypeDecl
  = DataDecl
    { typeDeclSrcSpan :: SrcSpan
    , typeDeclIdent   :: DeclIdent
    , typeDeclArgs    :: [TypeVarDecl]
    , dataDeclCons    :: [ConDecl]
    }
  | TypeSynDecl
    { typeDeclSrcSpan :: SrcSpan
    , typeDeclIdent   :: DeclIdent
    , typeDeclArgs    :: [TypeVarDecl]
    , typeSynDeclRhs  :: Type
    }
 deriving (Eq, Show)

-- | Gets the qualified name of the given type declaration.
typeDeclQName :: TypeDecl -> QName
typeDeclQName = declIdentName . typeDeclIdent

-- | Gets the unqualified name of the given type declaration.
typeDeclName :: TypeDecl -> Name
typeDeclName = nameFromQName . typeDeclQName

-- | Pretty instance for type declarations.
instance Pretty TypeDecl where
  pretty (DataDecl _ declIdent typeVarDecls conDecls) =
    prettyString "data"
      <+> pretty declIdent
      <+> hsep (map pretty typeVarDecls)
      <+> align (vcat (zipWith prettyConDecl [0 ..] conDecls))
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
data ConDecl = ConDecl
  { conDeclSrcSpan :: SrcSpan
  , conDeclIdent   :: DeclIdent
  , conDeclFields  :: [Type]
  }
 deriving (Eq, Show)

-- | Gets the qualified name of the given constructor declaration.
conDeclQName :: ConDecl -> QName
conDeclQName = declIdentName . conDeclIdent

-- | Gets the unqualified name of the given constructor declaration.
conDeclName :: ConDecl -> Name
conDeclName = nameFromQName . conDeclQName

-- | Pretty instance for data constructor declarations.
instance Pretty ConDecl where
  pretty (ConDecl _ declIdent types) =
    pretty declIdent <+> hsep (map pretty types)

-------------------------------------------------------------------------------
-- Type signatures                                                           --
-------------------------------------------------------------------------------

-- | A type signature of one or more function declarations.
data TypeSig = TypeSig
  { typeSigSrcSpan    :: SrcSpan
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

-- | Gets the qualified name of the given function declaration.
funcDeclQName :: FuncDecl -> QName
funcDeclQName = declIdentName . funcDeclIdent

-- | Gets the unqualified name of the given function declaration.
funcDeclName :: FuncDecl -> Name
funcDeclName = nameFromQName . funcDeclQName

-- | Gets the type of the given function declaration or @Nothing@ if at
--   least one of the argument or return type is not annotated.
--
--   In contrast to 'funcDeclTypeSchema' the function's type arguments
--   are not abstracted away.
funcDeclType :: FuncDecl -> Maybe Type
funcDeclType funcDecl = do
  argTypes <- mapM varPatType (funcDeclArgs funcDecl)
  retType  <- funcDeclReturnType funcDecl
  return (funcType NoSrcSpan argTypes retType)

-- | Gets the type schema of the given function declaration or @Nothing@
--   if at least one of the argument or the return type is not annotated.
funcDeclTypeSchema :: FuncDecl -> Maybe TypeSchema
funcDeclTypeSchema funcDecl =
  TypeSchema NoSrcSpan (funcDeclTypeArgs funcDecl) <$> funcDeclType funcDecl

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
      pretty declIdent <+> hsep (map ((char '@' <>) . pretty) typeArgs) <+> hsep
        (map pretty args)

-------------------------------------------------------------------------------
-- Type schemas                                                          --
-------------------------------------------------------------------------------

-- | A type expression with explicitly introduced type variables.
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

-- | A type expression.
--
--   Build-in types are represented by applications of their type constructors.
--   E.g. the type @[a]@ is represented as
--   @'TypeApp' ('TypeCon' "[]") ('TypeVar' "a")@.
--   The only exception to this rule is the function type @a -> b@. It is
--   represented directly as @'FuncType' ('TypeVar' "a") ('TypeVar' "b")@.
--   The syntax @(->) a b@ is not supported at the moment. This is due to the
--   special role of functions during the translation to Coq.
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
  :: SrcSpan -- ^ The source span to insert into generated nodes.
  -> Type    -- ^ The partially applied type constructor.
  -> [Type]  -- ^ The type arguments to pass to the type constructor.
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

-- | Pretty instance for type expressions.
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

-- | An expression.
data Expr
  = -- | A constructor.
    Con { exprSrcSpan    :: SrcSpan
        , exprConName    :: ConName
        , exprTypeSchema :: Maybe TypeSchema
        }

  | -- | A function or local variable.
    Var { exprSrcSpan    :: SrcSpan
        , exprVarName    :: VarName
        , exprTypeSchema :: Maybe TypeSchema
        }

  | -- | Function or constructor application.
    App { exprSrcSpan    :: SrcSpan
        , exprAppLhr     :: Expr
        , exprAppRhs     :: Expr
        , exprTypeSchema :: Maybe TypeSchema
        }

  | -- | Visible type application.
    TypeAppExpr { exprSrcSpan    :: SrcSpan
                , exprTypeAppLhs :: Expr
                , exprTypeAppRhs :: Type
                , exprTypeSchema :: Maybe TypeSchema
                }

  | -- | @if@ expression.
    If { exprSrcSpan    :: SrcSpan
       , ifExprCond     :: Expr
       , ifExprThen     :: Expr
       , ifExprElse     :: Expr
       , exprTypeSchema :: Maybe TypeSchema
       }

  | -- | @case@ expression.
    Case { exprSrcSpan       :: SrcSpan
         , caseExprScrutinee :: Expr
         , caseExprAlts      :: [Alt]
         , exprTypeSchema    :: Maybe TypeSchema
         }

  | -- | Error term @undefined@.
    Undefined { exprSrcSpan :: SrcSpan
              , exprTypeSchema :: Maybe TypeSchema
              }

  | -- | Error term @error "<message>"@.
    ErrorExpr { exprSrcSpan    :: SrcSpan
              , errorExprMsg   :: String
              , exprTypeSchema :: Maybe TypeSchema
              }

  | -- | An integer literal.
    IntLiteral { exprSrcSpan     :: SrcSpan
               , intLiteralValue :: Integer
               , exprTypeSchema  :: Maybe TypeSchema
               }

  | -- | A lambda abstraction.
    Lambda { exprSrcSpan    :: SrcSpan
           , lambdaExprArgs :: [VarPat]
           , lambdaEprRhs   :: Expr
           , exprTypeSchema :: Maybe TypeSchema
           }
 deriving (Eq, Show)

-- | Gets the type annotation of the given expression but discards the @forall@.
--
--   Type annotations quantify their type variables usually only if they are
--   as expression type signatures. The type annotations generated during
--   type inference never quantify their type arguments.
exprType :: Expr -> Maybe Type
exprType = exprTypeSchema >=> \(TypeSchema _ typeArgs typeExpr) ->
  if null typeArgs then Just typeExpr else Nothing

-- | Smart constructor for 'Con' without the last argument.
untypedCon :: SrcSpan -> ConName -> Expr
untypedCon srcSpan conName = Con srcSpan conName Nothing

-- | Smart constructor for 'Var' without the last argument.
untypedVar :: SrcSpan -> ConName -> Expr
untypedVar srcSpan varName = Var srcSpan varName Nothing

-- | Smart constructor for 'app' without the last argument.
--
--   The type annotation is inferred from the callee's type annotation.
--   If it is annotated with a function type, the  created expression
--   is annotated with the function type's result type.
untypedApp :: SrcSpan -> Expr -> Expr -> Expr
untypedApp srcSpan e1 e2 = App srcSpan e1 e2 appType
 where
  -- | The type to annotate the application with.
  appType :: Maybe TypeSchema
  appType = exprTypeSchema e1 >>= maybeFuncResTypeSchema

  -- | If the given type schema has the form @forall α₁ … αₙ. τ -> τ'@, the
  --   result has the form @forall α₁ … αₙ. τ'@. Returns @Nothing@ otherwise.
  maybeFuncResTypeSchema :: TypeSchema -> Maybe TypeSchema
  maybeFuncResTypeSchema (TypeSchema srcSpan' typeArgs typeExpr) =
    TypeSchema srcSpan' typeArgs <$> maybeFuncResType typeExpr

  -- | If the given type schema has the form @τ -> τ'@, the result has the
  --   form @τ'@. Returns @Nothing@ otherwise.
  maybeFuncResType :: Type -> Maybe Type
  maybeFuncResType (FuncType _ _ resType) = Just resType
  maybeFuncResType _                      = Nothing

-- | Creates an expression for applying the given expression to the provided
--   arguments.
--
--   The given source span is inserted into the generated function application
--   expressions.
--
--   If the given expression's type is annotated with a function type, all
--   generated application nodes are annotated with the corresponding result
--   types. If no more argument types can be split off, the types of the
--   remaining arguments are not annotated.
app :: SrcSpan -> Expr -> [Expr] -> Expr
app = foldl . untypedApp

-- | Creates an expression for applying the function with the given name.
--
--   The given source span is inserted into the generated function reference
--   and every generated function application.
--
--   Since the type of the variable with the given name is not known,
--   no type annotations will be generated.
varApp
  :: SrcSpan -- ^ The source span to insert into generated nodes.
  -> VarName -- ^ The name of the function to apply.
  -> [Expr]  -- ^ The arguments to pass to the function.
  -> Expr
varApp srcSpan = app srcSpan . untypedVar srcSpan

-- | Creates a data constructor application expression.
--
--   The given source span is inserted into the generated constructor reference
--   and every generated constructor application.
--
--   Since the type of the constructor with the given name is not known,
--   no type annotations will be generated.
conApp
  :: SrcSpan -- ^ The source span to insert into generated nodes.
  -> ConName -- ^ The name of the constructor to apply.
  -> [Expr]  -- ^ The arguments to pass to the constructor.
  -> Expr
conApp srcSpan = app srcSpan . untypedCon srcSpan

-- | Creates an expression for passing the type arguments of a function or
--   constructor explicitly.
--
--   The given source span is inserted into every generated visible type
--   application node.
--
--   If the given expression's type is annotated, all generated visible
--   type application nodes are annotated with the same type.
visibleTypeApp :: SrcSpan -> Expr -> [Type] -> Expr
visibleTypeApp srcSpan =
  foldl (\e t -> TypeAppExpr srcSpan e t (exprTypeSchema e))

-- | Pretty instance for expressions.
--
--   To improve the readability of the pretty printed expressions, type
--   annotations are not printed except for type annotations of variable
--   patterns. Visible type applications are printed.
instance Pretty Expr where
  pretty = prettyExprPred 0

-- | Pretty prints an expression and adds parenthesis if necessary.
--
--   The first argument indicates the precedence of the surrounding
--   context.
--    * @0@ - Top level. No parenthesis are necessary.
--    * @1@ - Parenthesis are needed around @if@, @case@ and lambda
--            expressions.
--    * @2@ - Parenthesis are also needed around function applications.
prettyExprPred :: Int -> Expr -> Doc

-- Parenthesis can be omitted around @if@, @case@, lambda abstractions only.
prettyExprPred 0 (If _ e1 e2 e3 _) =
  prettyString "if"
    <+> prettyExprPred 1 e1
    <+> prettyString "then"
    <+> prettyExprPred 0 e2
    <+> prettyString "else"
    <+> prettyExprPred 0 e3
prettyExprPred 0 (Case _ e alts _) =
  prettyString "case" <+> prettyExprPred 1 e <+> prettyString "of" <+> braces
    (space <> prettySeparated (semi <> space) (map pretty alts) <> space)
prettyExprPred 0 (Lambda _ args expr _) =
  backslash
    <>  hsep (map pretty args)
    <+> prettyString "->"
    <+> prettyExprPred 0 expr

-- At all other levels, the parenthesis cannot be omitted.
prettyExprPred _ expr@(If _ _ _ _ _  ) = parens (pretty expr)
prettyExprPred _ expr@(Case   _ _ _ _) = parens (pretty expr)
prettyExprPred _ expr@(Lambda _ _ _ _) = parens (pretty expr)

-- Fix placement of visible type arguments in for error terms.
prettyExprPred n (TypeAppExpr _ (ErrorExpr _ msg _) t _) | n <= 1 =
  prettyString "error" <+> char '@' <> prettyTypePred 2 t <+> prettyString
    (show msg)

-- Function application is left-associative.
prettyExprPred n expr@(App _ e1 e2 _)
  | n <= 1    = prettyExprPred 1 e1 <+> prettyExprPred 2 e2
  | otherwise = parens (pretty expr)
prettyExprPred n expr@(TypeAppExpr _ e t _)
  | n <= 1    = prettyExprPred 1 e <+> char '@' <> prettyTypePred 2 t
  | otherwise = parens (pretty expr)
prettyExprPred n expr@(ErrorExpr _ msg _)
  | n <= 1    = prettyString "error" <+> prettyString (show msg)
  | otherwise = parens (pretty expr)

-- No parenthesis are needed around variable and constructor names and
-- integer literals.
prettyExprPred _ (Con        _ name _) = pretty name
prettyExprPred _ (Var        _ name _) = pretty name
prettyExprPred _ (IntLiteral _ i    _) = integer i
prettyExprPred _ (Undefined _ _      ) = prettyString "undefined"

-------------------------------------------------------------------------------
-- @case@ expression alternatives                                            --
-------------------------------------------------------------------------------

-- | One alternative of a @case@ expression.
data Alt = Alt
  { altSrcSpan :: SrcSpan
  , altConPat  :: ConPat
  , altVarPats :: [VarPat]
  , altRhs     :: Expr
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
conPatToExpr (ConPat srcSpan conName) = Con srcSpan conName Nothing

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
  , varPatType    :: Maybe Type
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
varPatToExpr (VarPat srcSpan varName _) =
  Var srcSpan (UnQual (Ident varName)) Nothing

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

-- | When inferring the type of 'IntLiteral's this is the type to infer.
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
