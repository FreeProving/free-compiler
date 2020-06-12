-- | This module contains functions for converting type synonym and data type
--   declarations and their constructors.

module FreeC.Backend.Agda.Converter.TypeDecl
  ( convertTypeDecl
  )
where

import qualified FreeC.IR.Syntax               as IR
import qualified FreeC.IR.SrcSpan              as IR
                                                ( SrcSpan(NoSrcSpan) )
import qualified FreeC.Backend.Agda.Syntax     as Agda
import           FreeC.Backend.Agda.Converter.Free
import           FreeC.Backend.Agda.Converter.Type
                                                ( convertConstructorType )
import           FreeC.Backend.Agda.Converter.Arg
                                                ( lookupTypeIdent
                                                , lookupValueIdent
                                                , convertTypeVarDecl
                                                )
import           FreeC.Monad.Converter          ( Converter
                                                , localEnv
                                                )

-- | Converts a data or type synonym declaration.
convertTypeDecl :: IR.TypeDecl -> Converter Agda.Declaration
convertTypeDecl (IR.TypeSynDecl _ _     _     _      ) = error "Not Supported"
convertTypeDecl (IR.DataDecl    _ ident tVars constrs) = localEnv
  (   freeDataDecl
  <$> lookupTypeIdent ident
  <*> mapM convertTypeVarDecl tVars
  <*> convertConstructors ident tVars constrs
  )

-- | Converts all constructors of a data declaration.
convertConstructors
  :: IR.DeclIdent     -- ^ The identifier of the data type.
  -> [IR.TypeVarDecl] -- ^ The type parameters declared by the data type.
  -> [IR.ConDecl]     -- ^ The constructor declarations of the data type.
  -> Converter [Agda.Declaration]
convertConstructors dataIdent tVars =
  mapM $ convertConstructor $ applyTVars dataIdent tVars

-- | Converts a single constructor of a (non-recursive) data type.
convertConstructor :: IR.Type -> IR.ConDecl -> Converter Agda.Declaration
convertConstructor retType (IR.ConDecl _ ident argTs) =
  Agda.funcSig
    <$> lookupValueIdent ident
    <*> convertConstructorType argTs retType

-- | Applies the list of type vars to the given identifier of a type constructor.
--
--   We synthesize the return type of the constructor in IR to avoid passing the
--   identifier and all used type variables to the type converter. This way we
--   can reuse the existing translation.
applyTVars :: IR.DeclIdent -> [IR.TypeVarDecl] -> IR.Type
applyTVars (IR.DeclIdent srcSpan ident) ts = foldl
  (IR.TypeApp IR.NoSrcSpan)
  (IR.TypeCon srcSpan ident)
  (map IR.typeVarDeclToType ts)
