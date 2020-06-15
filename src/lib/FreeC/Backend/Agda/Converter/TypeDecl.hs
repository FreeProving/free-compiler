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
import qualified FreeC.Backend.Agda.Base       as Agda.Base
import           FreeC.Backend.Agda.Converter.Free
import           FreeC.Backend.Agda.Converter.Type
                                                ( convertConstructorType )
import           FreeC.Backend.Agda.Converter.Arg
                                                ( convertTypeVarDecl
                                                , lookupValueIdent
                                                , lookupTypeIdent
                                                , lookupSmartIdent
                                                )
import           FreeC.Environment.Fresh        ( freshAgdaVar )
import           FreeC.Monad.Converter          ( Converter
                                                , localEnv
                                                )


-- | Converts a data or type synonym declaration.
convertTypeDecl :: IR.TypeDecl -> Converter [Agda.Declaration]
convertTypeDecl (IR.TypeSynDecl _ _ _ _) = error "At the Moment Not Supported"
convertTypeDecl (IR.DataDecl _ ident tVars constrs) =
  (:) <$> convertDataDecl ident tVars constrs <*> convertSmartConstrs constrs

-- | Converts a data declaration.
convertDataDecl
  :: IR.DeclIdent
  -> [IR.TypeVarDecl]
  -> [IR.ConDecl]
  -> Converter Agda.Declaration
convertDataDecl ident tVars constrs =
  localEnv
    $   freeDataDecl
    <$> lookupTypeIdent ident
    <*> mapM convertTypeVarDecl tVars
    <*> convertConstructors ident tVars constrs

-- | Converts all constructors of a data declaration.
--
--   We synthesize the return type of the constructor in IR to avoid passing the
--   identifier and all used type variables to the type converter. This way we
--   can reuse the existing translation.
convertConstructors
  :: IR.DeclIdent     -- ^ The identifier of the data type.
  -> [IR.TypeVarDecl] -- ^ The type parameters declared by the data type.
  -> [IR.ConDecl]     -- ^ The constructor declarations of the data type.
  -> Converter [Agda.Declaration]
convertConstructors (IR.DeclIdent srcSpan ident) tVars =
  mapM $ convertConstructor $ IR.typeApp IR.NoSrcSpan
                                         (IR.TypeCon srcSpan ident)
                                         (map IR.typeVarDeclToType tVars)

-- | Converts a single constructor of a (non-recursive) data type.
convertConstructor :: IR.Type -> IR.ConDecl -> Converter Agda.Declaration
convertConstructor retType (IR.ConDecl _ ident argTs) =
  Agda.funcSig
    <$> lookupValueIdent ident
    <*> convertConstructorType argTs retType

-- | Converts a list of constructors to a list of smart constructors.
convertSmartConstrs :: [IR.ConDecl] -> Converter [Agda.Declaration]
convertSmartConstrs = mapM convertSmartConstr

-- | Converts a single constructor to a smart constructor, which wraps the normal
--   constructor in the @Free@ monad using @pure@.
--
--   We use Agda's @pattern@ declarations for smart constructors to simplify
--   pattern matching in proofs.
convertSmartConstr :: IR.ConDecl -> Converter Agda.Declaration
convertSmartConstr (IR.ConDecl _ ident argTs) = do
  smartName <- lookupSmartIdent ident
  patternDecl smartName (repeat "x" `zip` argTs) $ \vars -> do
    normalName <- Agda.IdentP . Agda.qname' <$> lookupValueIdent ident
    let pureVal = foldl Agda.appP normalName vars
    pure (Agda.IdentP (Agda.qname' Agda.Base.pure) `Agda.appP` pureVal)

-- | Creates a new pattern declaration binding variables with the given names
--   and types.
patternDecl
  :: Agda.Name
  -- ^ Name of the declaration.
  -> [(String, IR.Type)]
  -- ^ Types and preferred names for the bound variables.
  -> ([Agda.Pattern] -> Converter Agda.Pattern)
  -- ^ Continuation for creating the definition using the new variables.
  -> Converter Agda.Declaration
patternDecl name vars k = localEnv $ do
  names <- mapM (uncurry freshAgdaVar) vars
  let decls = map (Agda.Arg Agda.defaultArgInfo . Agda.unqualify) names
  let varPatterns = map Agda.IdentP names
  Agda.patternSyn name decls <$> k varPatterns
