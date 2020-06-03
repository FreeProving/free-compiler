-- | This module contains the definition of type schemas of our intermediate
--   language.

module FreeC.IR.Syntax.TypeSchema where

import           FreeC.IR.SrcSpan
import           FreeC.IR.Syntax.Type
import           FreeC.IR.Syntax.TypeVarDecl
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Type schemas                                                          --
-------------------------------------------------------------------------------

-- | A type expression with explicitly introduced type variables.
data TypeSchema = TypeSchema
  { typeSchemaSrcSpan :: SrcSpan
  , typeSchemaArgs    :: [TypeVarDecl]
  , typeSchemaType    :: Type
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
