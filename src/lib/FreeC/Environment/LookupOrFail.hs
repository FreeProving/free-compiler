-- | This module contains functions to lookup entries of the 'Environment'
--   that (in contrast to the functions defined in "FreeC.Environment")
--   report a fatal error message when there is no such entry.
module FreeC.Environment.LookupOrFail where

import           Data.Composition               ( (.:)
                                                , (.:.)
                                                )

import qualified FreeC.Backend.Agda.Syntax     as Agda
import qualified FreeC.Backend.Coq.Syntax      as Coq
import           FreeC.Environment
import           FreeC.Environment.Entry
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pretty

-- | Looks up an entry of the environment with the given name or reports
--   a fatal error message if the identifier has not been defined or the
--   name is ambiguous.
--
--   If an error is reported, it points to the given source span.
lookupEntryOrFail :: SrcSpan -> IR.Scope -> IR.QName -> Converter EnvEntry
lookupEntryOrFail srcSpan scope name = do
  maybeEntry <- inEnv $ lookupEntry scope name
  case maybeEntry of
    Just entry -> return entry
    Nothing ->
      reportFatal
        $  Message srcSpan Error
        $  "Identifier not in scope '"
        ++ showPretty name
        ++ "'"

-- | Looks up the Coq identifier for a Haskell function, (type)
--   constructor or (type) variable with the given name or reports a fatal
--   error message if the identifier has not been defined.
--
--   If an error is reported, it points to the given source span.
lookupIdentOrFail
  :: SrcSpan  -- ^ The source location where the identifier is requested.
  -> IR.Scope -- ^ The scope to look the identifier up in.
  -> IR.QName -- ^ The Haskell identifier to look up.
  -> Converter Coq.Qualid
lookupIdentOrFail srcSpan scope name =
  entryIdent <$> lookupEntryOrFail srcSpan scope name

-- | Looks up the Agda identifier for a Haskell function, (type)
--   constructor or (type) variable with the given name or reports a fatal
--   error message if the identifier has not been defined.
--
--   If an error is reported, it points to the given source span.
lookupAgdaIdentOrFail
  :: SrcSpan  -- ^ The source location where the identifier is requested.
  -> IR.Scope -- ^ The scope to look the identifier up in.
  -> IR.QName -- ^ The Haskell identifier to look up.
  -> Converter Agda.QName
lookupAgdaIdentOrFail srcSpan scope name =
  entryAgdaIdent <$> lookupEntryOrFail srcSpan scope name

-- | Looks up an Agda identifier from the @IR.ValueScope@.
lookupAgdaValIdentOrFail :: SrcSpan -> IR.QName -> Converter Agda.QName
lookupAgdaValIdentOrFail = flip lookupAgdaIdentOrFail IR.ValueScope

-- | Looks up an Agda identifier from the 'IR.FreshScope'.
lookupAgdaFreshIdentOrFail :: SrcSpan -> IR.QName -> Converter Agda.QName
lookupAgdaFreshIdentOrFail = flip lookupAgdaIdentOrFail IR.FreshScope

-- | Looks up an Agda identifier from the @IR.TypeScope@.
lookupAgdaTypeIdentOrFail :: SrcSpan -> IR.QName -> Converter Agda.QName
lookupAgdaTypeIdentOrFail = flip lookupAgdaIdentOrFail IR.TypeScope

-- | Looks up an Agda identifier and unqualifies the name.
lookupUnQualAgdaIdentOrFail
  :: SrcSpan -> IR.Scope -> IR.QName -> Converter Agda.Name
lookupUnQualAgdaIdentOrFail = fmap Agda.unqualify .:. lookupAgdaIdentOrFail

-- | Looks up the Coq identifier of a smart constructor of the Haskell
--   data constructor with the given name or reports a fatal error message
--   if there is no such constructor.
--
--   If an error is reported, it points to the given source span.
lookupSmartIdentOrFail
  :: SrcSpan  -- ^ The source location where the identifier is requested.
  -> IR.QName -- ^ The Haskell identifier to look up.
  -> Converter Coq.Qualid
lookupSmartIdentOrFail srcSpan name =
  entrySmartIdent <$> lookupEntryOrFail srcSpan IR.ValueScope name

-- | Looks up the Agda identifier of a smart constructor of the Haskell
--   data constructor with the given name or reports a fatal error message
--   if there is no such constructor.
--
--   If an error is reported, it points to the given source span.
lookupAgdaSmartIdentOrFail
  :: SrcSpan  -- ^ The source location where the identifier is requested.
  -> IR.QName -- ^ The Haskell identifier to look up.
  -> Converter Agda.QName
lookupAgdaSmartIdentOrFail srcSpan name =
  entryAgdaSmartIdent <$> lookupEntryOrFail srcSpan IR.ValueScope name

-- | Looks up the Agda identifier of a smart constructor of the Haskell
--   data constructor with the given name and unqualifies it or reports
--   a fatal error message if there is no such constructor.
--
--   If an error is reported, it points to the given source span.
lookupUnQualAgdaSmartIdentOrFail
  :: SrcSpan  -- ^ The source location where the identifier is requested.
  -> IR.QName -- ^ The Haskell identifier to look up.
  -> Converter Agda.Name
lookupUnQualAgdaSmartIdentOrFail =
  fmap Agda.unqualify .: lookupAgdaSmartIdentOrFail
