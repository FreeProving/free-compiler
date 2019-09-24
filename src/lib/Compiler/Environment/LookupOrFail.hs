-- | This module contains functions to lookup entries of the 'Environment'
--   that (in constrast to the functions defined in "Compiler.Environment")
--   report a fatal error message when there is no such entry.

module Compiler.Environment.LookupOrFail where

import qualified Compiler.Coq.AST              as G
import           Compiler.Environment
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty

-- | Looks up the Coq identifier for a Haskell function, (type/smart)
--   constructor or (type) variable with the given name or reports a fatal
--   error message if the identifier has not been defined.
--
--   If an error is reported, it points to the given source span.
lookupIdentOrFail
  :: SrcSpan -- ^ The source location where the identifier is requested.
  -> Scope   -- ^ The scope to look the identifier up in.
  -> HS.Name -- ^ The Haskell identifier to look up.
  -> Converter G.Qualid
lookupIdentOrFail srcSpan scope name = do
  mQualid <- inEnv $ lookupIdent scope name
  case mQualid of
    Just qualid -> return qualid
    Nothing ->
      reportFatal
        $ Message srcSpan Error
        $ ("Unknown " ++ showPretty scope ++ ": " ++ showPretty name)

-- | Looks up the annoated type of a user defined function with the given name
--   and reports a fatal error message if there is no such type signature.
--
--   If an error is encountered, the reported message points to the given
--   source span.
lookupTypeSigOrFail :: SrcSpan -> HS.Name -> Converter HS.Type
lookupTypeSigOrFail srcSpan ident = do
  mTypeExpr <- inEnv $ lookupTypeSig ident
  case mTypeExpr of
    Just typeExpr -> return typeExpr
    Nothing ->
      reportFatal
        $ Message srcSpan Error
        $ ("Missing type signature for " ++ showPretty ident)
