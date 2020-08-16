-- | This module contains the definition of type variable declarations of our
--   intermediate language.
module FreeC.IR.Syntax.TypeVarDecl where

import           FreeC.IR.SrcSpan
import           FreeC.IR.Syntax.Name
import           FreeC.IR.Syntax.Type
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Type arguments                                                            --
-------------------------------------------------------------------------------
-- | The name of a type variable declaration in the head of a data type or
--   type synonym declaration including location information.
data TypeVarDecl
  = TypeVarDecl { typeVarDeclSrcSpan :: SrcSpan, typeVarDeclIdent :: String }
 deriving ( Eq, Show )

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
