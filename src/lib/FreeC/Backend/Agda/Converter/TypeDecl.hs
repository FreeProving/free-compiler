-- | This module contains functions for converting type synonym and data type
--   declarations and their constructors.
module FreeC.Backend.Agda.Converter.TypeDecl ( convertTypeDecls ) where

import           Data.List.Extra                   ( snoc )

import qualified FreeC.Backend.Agda.Base           as Agda.Base
import           FreeC.Backend.Agda.Converter.Arg  ( convertTypeVarDecl )
import           FreeC.Backend.Agda.Converter.Free
import           FreeC.Backend.Agda.Converter.Size
import           FreeC.Backend.Agda.Converter.Type ( convertLiftedConType )
import qualified FreeC.Backend.Agda.Syntax         as Agda
import           FreeC.Environment.Fresh           ( freshAgdaVar )
import           FreeC.Environment.LookupOrFail
import           FreeC.IR.DependencyGraph
import           FreeC.IR.SrcSpan                  ( SrcSpan(NoSrcSpan) )
import qualified FreeC.IR.Syntax                   as IR
import           FreeC.LiftedIR.Converter.Type     ( liftConArgType, liftType' )
import           FreeC.Monad.Converter             ( Converter, localEnv )
import           FreeC.Monad.Reporter
  ( Message(Message), Severity(Error), reportFatal )

-- | Converts a strongly connected component of the type dependency graph.
--   TODO: handle mutual recursive types
convertTypeDecls
  :: DependencyComponent IR.TypeDecl -> Converter [Agda.Declaration]
convertTypeDecls comp = case comp of
  NonRecursive decl -> convertTypeDecl decl False
  Recursive [decl]  -> convertTypeDecl decl True
  Recursive ds      -> reportFatal
    $ Message (IR.typeDeclSrcSpan $ head ds) Error
    $ "Mutual recursive data types are not supported by the Agda back end "
    ++ "at the moment."

-- | Converts a data or type synonym declaration.
--   TODO: Convert type synonyms.
convertTypeDecl :: IR.TypeDecl -> Bool -> Converter [Agda.Declaration]
convertTypeDecl (IR.TypeSynDecl srcSpan _ _ _) _          = reportFatal
  $ Message srcSpan Error
  $ "Type synonyms are not supported by the Agda back end at the moment."
convertTypeDecl (IR.DataDecl _ ident tVars constrs) isRec = (:)
  <$> convertDataDecl ident tVars constrs isRec
  <*> mapM generateSmartConDecl constrs

-- | Converts a data declaration by creating an Agda data type of the
--   (preferably) same name and lifting constructors piecewise using
--   @convertConDecl@.
--
--   An IR data type declaration of the form
--
--   > data D α₁ … αₙ
--   >   = C₁ τ₁ … τᵢ
--   >   ⋮
--   >   | Cₘ ρ₁ … ρⱼ
--
--   is converted into into an Agda data type of the following form.
--
--   > data D̂ (Shape : Set)(Pos : Shape → Set)(α̂₁ … α̂ₙ : Set) : Set where
--   >   Ĉ₁ : τ₁̓ → … → τᵢ̓ → D̂ Shape Pos α̂₁ … α̂ₙ
--   >     ⋮
--   >   Ĉₘ : ρ₁̓ → … → ρⱼ̓ → D̂ Shape Pos α̂₁ … α̂ₙ
--
--   Environment entries for the type arguments @α̂₁ … α̂ₙ@ are only visible
--   within the data type declaration.
convertDataDecl :: IR.DeclIdent     -- ^ The name of the data type
                -> [IR.TypeVarDecl] -- ^ Type parameters for the data type.
                -> [IR.ConDecl]     -- ^ The constructors for this data type.
                -> Bool             -- ^ Is this a recursive data declaration?
                -> Converter Agda.Declaration
convertDataDecl ident@(IR.DeclIdent srcSpan name) typeVars constrs isRec
  = localEnv
  $ freeDataDecl <$> lookupUnQualAgdaIdentOrFail srcSpan IR.TypeScope name
  <*> mapM convertTypeVarDecl typeVars
  <*> pure universe
  <*> convertConDecls ident typeVars constrs
 where
   universe
     = if isRec then Agda.hiddenArg_ size `Agda.fun` Agda.set else Agda.set

-- | Converts all constructors of a data declaration.
--
--   We synthesize the return type of the constructor in IR to avoid passing the
--   identifier and all used type variables to the type converter. This way we
--   can reuse the existing translation.
convertConDecls
  :: IR.DeclIdent     -- ^ The identifier of the data type.
  -> [IR.TypeVarDecl] -- ^ The type parameters declared by the data type.
  -> [IR.ConDecl]     -- ^ The constructor declarations of the data type.
  -> Converter [Agda.Declaration]
convertConDecls (IR.DeclIdent srcSpan ident) typeVars
  = mapM $ convertConDecl ident constructedType
 where
   constructedType = IR.typeApp NoSrcSpan (IR.TypeCon srcSpan ident)
     $ map IR.typeVarDeclToType typeVars

-- | Converts a single constructor of a data type.
convertConDecl
  :: IR.QName -> IR.Type -> IR.ConDecl -> Converter Agda.Declaration
convertConDecl ident retType (IR.ConDecl _ (IR.DeclIdent srcSpan name) argTypes)
  = do
    argTypes' <- mapM (liftConArgType ident) argTypes
    retType' <- liftType' retType
    -- TODO: Add declarations to lifted IR and move this translation logic.
    Agda.funcSig <$> lookupUnQualAgdaIdentOrFail srcSpan IR.ValueScope name
      <*> convertLiftedConType argTypes' retType'

-- | Converts a single constructor to a smart constructor, which wraps the normal
--   constructor in the @Free@ monad using @pure@.
--
--   We use Agda's @pattern@ declarations for smart constructors to simplify
--   pattern matching in proofs.
generateSmartConDecl :: IR.ConDecl -> Converter Agda.Declaration
generateSmartConDecl (IR.ConDecl _ (IR.DeclIdent srcSpan name) argTypes) = do
  smartName <- lookupUnQualAgdaSmartIdentOrFail srcSpan name
  patternDecl smartName (replicate (length argTypes) "x")
    $ \vars -> do
      normalName <- Agda.IdentP <$> lookupAgdaValIdentOrFail srcSpan name
      let pureVal = foldl Agda.appP normalName vars
      return (Agda.IdentP (Agda.qname' Agda.Base.pure) `Agda.appP` pureVal)

-------------------------------------------------------------------------------
-- Specialized Syntax                                                        --
-------------------------------------------------------------------------------
-- | Creates a declaration for a data type, which is parameterized over @Shape@
--   and @Pos@.
freeDataDecl :: Agda.Name          -- ^ Name of the data type
             -> [Agda.Name]        -- ^ Names of the bound type variables
             -> Agda.Expr          -- ^ Universe containing the declaration
             -> [Agda.Declaration] -- ^ List of constructor declarations
             -> Agda.Declaration
freeDataDecl dataName typeNames = Agda.dataDecl dataName
  (freeArgBinder `snoc` Agda.binding typeNames Agda.set)

-- | Creates a new pattern declaration binding variables with the given names
--   and types.
patternDecl
  :: Agda.Name
  -- ^ Name of the declaration.
  -> [String]
  -- ^ Types and preferred names for the bound variables.
  -> ([Agda.Pattern] -> Converter Agda.Pattern)
  -- ^ Continuation for creating the definition using the new variables.
  -> Converter Agda.Declaration
patternDecl name vars k = localEnv
  $ do
    names <- mapM freshAgdaVar vars
    let decls       = map (Agda.Arg Agda.defaultArgInfo . Agda.unqualify) names
        varPatterns = map Agda.IdentP names
    Agda.patternSyn name decls <$> k varPatterns
