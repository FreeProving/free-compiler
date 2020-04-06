-- | This module contains the definition of expressions for function
--   declarations and type signatures for our intermediate language.

module FreeC.IR.Syntax.FuncDecl where

import           FreeC.IR.SrcSpan
import           FreeC.IR.Syntax.Expr
import           FreeC.IR.Syntax.Name
import           FreeC.IR.Syntax.Type
import           FreeC.IR.Syntax.TypeSchema
import           FreeC.IR.Syntax.TypeVarDecl
import           FreeC.Pretty

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
  , funcDeclReturnType :: Maybe Type
    -- ^ The return type of the function.
  , funcDeclRhs        :: Expr
    -- ^ The right-hand side of the function declaration.
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
  pretty (FuncDecl _ declIdent typeArgs args maybeReturnType rhs) =
    case maybeReturnType of
      Nothing -> prettyFuncHead <+> equals <+> pretty rhs
      Just returnType ->
        prettyFuncHead
          <+> colon <> colon <+> pretty returnType
          <+> equals
          <+> pretty rhs
   where
    -- | The left-hand side of the function declaration.
    prettyFuncHead :: Doc
    prettyFuncHead =
      pretty declIdent <+> hsep (map ((char '@' <>) . pretty) typeArgs) <+> hsep
        (map pretty args)
