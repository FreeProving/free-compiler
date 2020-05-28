-- | This module contains the definition of expressions for our intermediate
--   language.

module FreeC.IR.Syntax.Expr where

import           Control.Monad                  ( (>=>) )

import           FreeC.IR.SrcSpan
import           FreeC.IR.Syntax.Name
import           FreeC.IR.Syntax.Type
import           FreeC.IR.Syntax.TypeSchema
import           FreeC.Pretty

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
    Undefined { exprSrcSpan    :: SrcSpan
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

-- | Smart constructor for 'TypeAppExpr' without the last argument.
--
--   The type annotation from the expression which is visibly applied is
--   used to annotate the type of this expression.
untypedTypeAppExpr :: SrcSpan -> Expr -> Type -> Expr
untypedTypeAppExpr srcSpan expr typeExpr =
  TypeAppExpr srcSpan expr typeExpr (exprTypeSchema expr)

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
visibleTypeApp = foldl . untypedTypeAppExpr

-- | Pretty instance for expressions.
--
--   If the expression contains type annotations, the output quickly becomes
--   practically unreadable. Consider stripping type annotations before
--   pretty printing (see "FreeC.IR.Strip") to improve readability.
instance Pretty Expr where
  pretty = prettyExprPred 0

-- | Pretty prints an expression and adds parenthesis if necessary.
--
--   The first argument indicates the precedence of the surrounding
--   context.
--    * @0@ - Top level. No parenthesis are necessary.
--    * @1@ - Parenthesis are needed around @if@ and lambda expressions.
--    * @2@ - Parenthesis are also needed around function applications.
prettyExprPred :: Int -> Expr -> Doc

-- If there is a type annotation, parenthesis are needed around @if@
-- expressions and lambda abstractions since their sub-expressions would
-- capture the type annotation otherwise.
prettyExprPred n expr = case exprTypeSchema expr of
  Nothing -> prettyExprPred' n expr
  Just typeSchema | n == 0    -> prettyExpr
                  | otherwise -> parens prettyExpr
   where
    prettyExpr :: Doc
    prettyExpr =
      prettyExprPred' 1 expr <+> colon <> colon <+> pretty typeSchema

-- | Like 'prettyExprPred' but ignores outermost type annotations.
prettyExprPred' :: Int -> Expr -> Doc

-- Due to the use of braces, parenthesis can be omitted around @case@
-- expressions even if they are not at top-level. However, if they are
-- used in function applications, parenthesis are needed.
prettyExprPred' n expr@(Case _ scrutinee alts _)
  | n <= 1
  = prettyString "case"
    <+> prettyExprPred 1 scrutinee
    <+> prettyString "of"
    <+> braces
          (space <> prettySeparated (semi <> space) (map pretty alts) <> space)
  | otherwise
  = parens (prettyExprPred' 1 expr)

-- Parenthesis can be omitted around @if@@ and lambda abstractions at
-- top-level only.
prettyExprPred' 0 (If _ e1 e2 e3 _) =
  prettyString "if"
    <+> prettyExprPred 1 e1
    <+> prettyString "then"
    <+> prettyExprPred 0 e2
    <+> prettyString "else"
    <+> prettyExprPred 0 e3
prettyExprPred' 0 (Lambda _ args expr _) =
  backslash
    <>  hsep (map pretty args)
    <+> prettyString "->"
    <+> prettyExprPred 0 expr

-- At all other levels, the parenthesis cannot be omitted.
prettyExprPred' _ expr@(If _ _ _ _ _  ) = parens (prettyExprPred' 0 expr)
prettyExprPred' _ expr@(Lambda _ _ _ _) = parens (prettyExprPred' 0 expr)

-- Fix placement of visible type arguments in error terms.
prettyExprPred' n (TypeAppExpr _ (ErrorExpr _ msg _) t _) | n <= 1 =
  prettyString "error" <+> char '@' <> prettyTypePred 2 t <+> prettyString
    (show msg)

-- Function application is left-associative.
prettyExprPred' n expr@(App _ e1 e2 _)
  | n <= 1    = prettyExprPred 1 e1 <+> prettyExprPred 2 e2
  | otherwise = parens (prettyExprPred' 1 expr)
prettyExprPred' n expr@(TypeAppExpr _ e t _)
  | n <= 1    = prettyExprPred 1 e <+> char '@' <> prettyTypePred 2 t
  | otherwise = parens (prettyExprPred' 1 expr)
prettyExprPred' n expr@(ErrorExpr _ msg _)
  | n <= 1    = prettyString "error" <+> prettyString (show msg)
  | otherwise = parens (prettyExprPred' 1 expr)

-- No parenthesis are needed around variable and constructor names and
-- integer literals.
prettyExprPred' _ (Con        _ name _) = pretty name
prettyExprPred' _ (Var        _ name _) = pretty name
prettyExprPred' _ (IntLiteral _ i    _) = integer i
prettyExprPred' _ (Undefined _ _      ) = prettyString "undefined"

-------------------------------------------------------------------------------
-- @case@ expression alternatives                                            --
-------------------------------------------------------------------------------

-- | One alternative of a @case@ expression.
--
--   The left hand side can be annotated by a @!@.
data Alt = Alt
  { altSrcSpan :: SrcSpan
  , altConPat  :: ConPat
  , altVarPats :: [VarPat]
  , altRhs     :: Expr
  , altIsBang  :: Bool
  }
 deriving (Eq, Show)

-- | Pretty instance for @case@ expression alternatives.
instance Pretty Alt where
  pretty (Alt _ conPat varPats expr False) =
    pretty conPat
      <+> hsep (map pretty varPats)
      <+> prettyString "->"
      <+> pretty expr
  pretty (Alt _ conPat varPats expr True) =
    char '!'
      <>  parens (pretty conPat <+> hsep (map pretty varPats))
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
--   The variable pattern can optionally have a type signature
--   or can be annotated by a @!@.
data VarPat = VarPat
  { varPatSrcSpan :: SrcSpan
  , varPatIdent   :: String
  , varPatType    :: Maybe Type
  , varPatIsBang  :: Bool
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
varPatToExpr (VarPat srcSpan varName _ _) =
  Var srcSpan (UnQual (Ident varName)) Nothing

-- | Converts the given identifier to a variable pattern without type
--   annotation.
toVarPat :: String -> VarPat
toVarPat ident = VarPat NoSrcSpan ident Nothing False

-- | Pretty instance for variable patterns.
instance Pretty VarPat where
  pretty (VarPat _ varName Nothing False) = pretty varName
  pretty (VarPat _ varName Nothing True ) = char '!' <> pretty varName
  pretty (VarPat _ varName (Just varType) False) =
    parens (pretty varName <+> colon <> colon <+> pretty varType)
  pretty (VarPat _ varName (Just varType) True) =
    char '!' <> parens (pretty varName <+> colon <> colon <+> pretty varType)
