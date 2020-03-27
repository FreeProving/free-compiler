-- | This module contains functions to lookup entries of the 'Environment'
--   that (in contrast to the functions defined in "Compiler.Environment")
--   report a fatal error message when there is no such entry.

module Compiler.Environment.LookupOrFail where

import qualified Compiler.Backend.Coq.Syntax              as G
import           Compiler.Environment
import           Compiler.Environment.Entry
import           Compiler.Environment.Scope
import           Compiler.IR.SrcSpan
import qualified Compiler.IR.Syntax            as HS
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty

-- | Looks up an entry of the environment with the given name or reports
--   a fatal error message if the identifier has not been defined or the
--   name is ambigious.
--
--   If an error is reported, it points to the given source span.
lookupEntryOrFail :: SrcSpan -> Scope -> HS.QName -> Converter EnvEntry
lookupEntryOrFail srcSpan scope name = do
  maybeEntry <- inEnv $ lookupEntry scope name
  case maybeEntry of
    Just entry -> return entry
    Nothing ->
      reportFatal
        $ Message srcSpan Error
        $ ("Identifier not in scope '" ++ showPretty name ++ "'")

-- | Looks up the Coq identifier for a Haskell function, (type)
--   constructor or (type) variable with the given name or reports a fatal
--   error message if the identifier has not been defined.
--
--   If an error is reported, it points to the given source span.
lookupIdentOrFail
  :: SrcSpan  -- ^ The source location where the identifier is requested.
  -> Scope    -- ^ The scope to look the identifier up in.
  -> HS.QName -- ^ The Haskell identifier to look up.
  -> Converter G.Qualid
lookupIdentOrFail srcSpan scope name = do
  entry <- lookupEntryOrFail srcSpan scope name
  return (entryIdent entry)

-- | Looks up the Coq identifier of a smart constructor of the Haskell
--   data constructr with the given name or reports a fatal error message
--   if there is no such constructor.
--
--   If an error is reported, it points to the given source span.
lookupSmartIdentOrFail
  :: SrcSpan  -- ^ The source location where the identifier is requested.
  -> HS.QName -- ^ The Haskell identifier to look up.
  -> Converter G.Qualid
lookupSmartIdentOrFail srcSpan name = do
  entry <- lookupEntryOrFail srcSpan ValueScope name
  return (entrySmartIdent entry)
