-- | This module contains the definition of type schemes of our intermediate
--   language.
module FreeC.IR.Syntax.TypeScheme where

import           FreeC.IR.SrcSpan
import           FreeC.IR.Syntax.Type
import           FreeC.IR.Syntax.TypeVarDecl
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Type Schemes                                                              --
-------------------------------------------------------------------------------
-- | A type expression with explicitly introduced type variables.
data TypeScheme = TypeScheme { typeSchemeSrcSpan :: SrcSpan
                             , typeSchemeArgs    :: [ TypeVarDecl ]
                             , typeSchemeType    :: Type
                             }
 deriving ( Eq, Show )

-- | Pretty instance for type schemes.
instance Pretty TypeScheme where
  pretty (TypeScheme _ [] typeExpr)       = pretty typeExpr
  pretty (TypeScheme _ typeArgs typeExpr) = prettyString "forall"
    <+> hsep (map pretty typeArgs) <> dot
    <+> pretty typeExpr
