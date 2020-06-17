-- | This module contains functions for converting type synonym and data type
--   declarations and their constructors.

module FreeC.Backend.Agda.Converter.TypeDecl
  ( convertTypeDecl
  )
where

import           Prelude                 hiding ( pi )

import           Data.Bool                      ( bool )
import           Data.List.Extra                ( snoc )

import qualified FreeC.IR.Syntax               as IR
import           FreeC.IR.SrcSpan               ( SrcSpan(NoSrcSpan) )
import qualified FreeC.Backend.Agda.Base       as Agda.Base
import           FreeC.Backend.Agda.Analysis.RecursiveDataType
import           FreeC.Backend.Agda.Converter.Free
import qualified FreeC.Backend.Agda.Syntax     as Agda
import           FreeC.Backend.Agda.Converter.Type
                                                ( convertConType
                                                , convertRecConType
                                                )
import           FreeC.Backend.Agda.Converter.Arg
                                                ( convertTypeVarDecl )
import           FreeC.Backend.Agda.Converter.Size
import           FreeC.Environment.Fresh        ( freshAgdaVar )
import           FreeC.Environment.LookupOrFail
import           FreeC.Monad.Converter          ( Converter
                                                , localEnv
                                                )

-- | Converts a data or type synonym declaration.
--   TODO: Convert type synonyms.
convertTypeDecl :: IR.TypeDecl -> Converter [Agda.Declaration]
convertTypeDecl (IR.TypeSynDecl _ _ _ _) = error "Not supported at the moment."
convertTypeDecl decl@(IR.DataDecl _ ident tVars constrs) =
  (:)
    <$> convertDataDecl ident tVars constrs (isRecursiveDataType decl)
    <*> mapM generateSmartConDecl constrs

-- | Converts a data declaration by creating an Agda data type of the
--  (preferably) same name and lifting constructors piecewise using
--  @convertConDecl@.
--
--  @Shape@ and @Pos@ are abbreviated for readability.
--  > data D α₁ … αₙ    data D̂ (S : Set)(P : S → Set)(α̂₁ … α̂ₙ : Set) : Set where
--  >   = C₁ τ₁ … τᵢ        Ĉ₁ : τ₁̓ → … → τᵢ̓ → D̂ S P α̂₁ … α̂ₙ
--  >                 ↦
--  >   | Cₘ ρ₁ … ρⱼ        Ĉₘ : ρ₁̓ → … → ρⱼ̓ → D̂ S P α̂₁ … α̂ₙ
convertDataDecl
  :: IR.DeclIdent     -- ^ The name of the data type
  -> [IR.TypeVarDecl] -- ^ Type parameters for the data type.
  -> [IR.ConDecl]     -- ^ The constructors for this data type.
  -> Bool             -- ^ Is this a recursive data declaration?
  -> Converter Agda.Declaration
convertDataDecl ident@(IR.DeclIdent srcSpan name) typeVars constrs isRec =
  localEnv -- The data declaration opens a new scope binding @S@, @P and α̂ᵢ.
    $   freeDataDecl
    <$> lookupUnQualAgdaIdentOrFail srcSpan IR.TypeScope name
    <*> mapM convertTypeVarDecl typeVars
    <*> pure universe
    <*> convertConDecl ident typeVars isRec constrs
 where
  universe =
    (if isRec then Agda.hiddenArg_ size `Agda.fun` Agda.set else Agda.set)

-- | Converts all constructors of a data declaration.
--
--   We synthesize the return type of the constructor in IR to avoid passing the
--   identifier and all used type variables to the type converter. This way we
--   can reuse the existing translation.
convertConDecl
  :: IR.DeclIdent     -- ^ The identifier of the data type.
  -> [IR.TypeVarDecl] -- ^ The type parameters declared by the data type.
  -> Bool             -- ^ Is this a recursive data declaration
  -> [IR.ConDecl]     -- ^ The constructor declarations of the data type.
  -> Converter [Agda.Declaration]
convertConDecl (IR.DeclIdent srcSpan ident) typeVars isRec =
  mapM $ convertConstructor (bool Nothing (Just ident) isRec) $ IR.typeApp
    NoSrcSpan
    (IR.TypeCon srcSpan ident)
    (map IR.typeVarDeclToType typeVars)

-- | Converts a single constructor of a (non-recursive) data type.
convertConstructor
  :: Maybe IR.QName -> IR.Type -> IR.ConDecl -> Converter Agda.Declaration
convertConstructor ident retType (IR.ConDecl _ (IR.DeclIdent srcSpan name) argTypes)
  = Agda.funcSig
    <$> lookupUnQualAgdaIdentOrFail srcSpan IR.ValueScope name
    <*> maybe convertConType convertRecConType ident argTypes retType

-- | Converts a single constructor to a smart constructor, which wraps the normal
--   constructor in the @Free@ monad using @pure@.
--
--   We use Agda's @pattern@ declarations for smart constructors to simplify
--   pattern matching in proofs.
generateSmartConDecl :: IR.ConDecl -> Converter Agda.Declaration
generateSmartConDecl (IR.ConDecl _ (IR.DeclIdent srcSpan name) argTypes) = do
  smartName <- lookupUnQualAgdaSmartIdentOrFail srcSpan name
  patternDecl smartName (repeat "x" `zip` argTypes) $ \vars -> do
    normalName <- Agda.IdentP <$> lookupAgdaValIdentOrFail srcSpan name
    let pureVal = foldl Agda.appP normalName vars
    return (Agda.IdentP (Agda.qname' Agda.Base.pure) `Agda.appP` pureVal)

-------------------------------------------------------------------------------
-- specialized syntax                                                        --
-------------------------------------------------------------------------------

-- | Creates a declaration for a data type, which is parameterized over @Shape@
--   and @Pos@.
freeDataDecl
  :: Agda.Name          -- ^ Name of the data type
  -> [Agda.Name]        -- ^ Names of the bound type variables
  -> Agda.Expr          -- ^ Universe containing the declaration
  -> [Agda.Declaration] -- ^ List of constructor declarations
  -> Agda.Declaration
freeDataDecl dataName typeNames =
  Agda.dataDecl dataName (freeArgBinder `snoc` Agda.binding typeNames Agda.set)

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

