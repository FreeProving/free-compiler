-- | This module contains the definition of data type and type synonym
--   declarations of our intermediate language.
module FreeC.IR.Syntax.TypeDecl where

import           FreeC.IR.SrcSpan
import           FreeC.IR.Syntax.Name
import           FreeC.IR.Syntax.Type
import           FreeC.IR.Syntax.TypeVarDecl
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Type Declarations                                                         --
-------------------------------------------------------------------------------
-- | A data type or type synonym declaration.
data TypeDecl
  = DataDecl { typeDeclSrcSpan :: SrcSpan
             , typeDeclIdent   :: DeclIdent
             , typeDeclArgs    :: [TypeVarDecl]
             , dataDeclCons    :: [ConDecl]
             }
  | TypeSynDecl { typeDeclSrcSpan :: SrcSpan
                , typeDeclIdent   :: DeclIdent
                , typeDeclArgs    :: [TypeVarDecl]
                , typeSynDeclRhs  :: Type
                }
 deriving ( Eq, Show )

-- | Gets the qualified name of the given type declaration.
typeDeclQName :: TypeDecl -> QName
typeDeclQName = declIdentName . typeDeclIdent

-- | Gets the unqualified name of the given type declaration.
typeDeclName :: TypeDecl -> Name
typeDeclName = nameFromQName . typeDeclQName

-- | Pretty instance for type declarations.
instance Pretty TypeDecl where
  pretty (DataDecl _ declIdent typeVarDecls conDecls) = prettyString "data"
    <+> pretty declIdent
    <+> hsep (map pretty typeVarDecls)
    <+> align (vcat (zipWith prettyConDecl [0 ..] conDecls))
   where
    prettyConDecl :: Int -> ConDecl -> Doc
    prettyConDecl i conDecl
      | i == 0 = equals <+> pretty conDecl
      | otherwise = char '|' <+> pretty conDecl
  pretty (TypeSynDecl _ declIdent typeVarDecls typeExpr) = prettyString "type"
    <+> pretty declIdent
    <+> hsep (map pretty typeVarDecls)
    <+> equals
    <+> pretty typeExpr

-------------------------------------------------------------------------------
-- Constructor Declarations                                                  --
-------------------------------------------------------------------------------
-- | A constructor declaration.
data ConDecl = ConDecl { conDeclSrcSpan :: SrcSpan
                       , conDeclIdent   :: DeclIdent
                       , conDeclFields  :: [Type]
                       }
 deriving ( Eq, Show )

-- | Gets the qualified name of the given constructor declaration.
conDeclQName :: ConDecl -> QName
conDeclQName = declIdentName . conDeclIdent

-- | Gets the unqualified name of the given constructor declaration.
conDeclName :: ConDecl -> Name
conDeclName = nameFromQName . conDeclQName

-- | Pretty instance for data constructor declarations.
instance Pretty ConDecl where
  pretty (ConDecl _ declIdent types) = pretty declIdent
    <+> hsep (map pretty types)
