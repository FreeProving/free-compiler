-- | This module contains a function for converting type schemas from Haskell
--   to Coq.

module Compiler.Converter.TypeSchema
  ( convertTypeSchema
  )
where

import           Compiler.Converter.Type
import qualified Compiler.Coq.AST              as G
import           Compiler.Environment
import           Compiler.Environment.Entry
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Converter

-- | Converts a Haskell type schema to Coq.
convertTypeSchema :: HS.TypeSchema -> Converter G.Term
convertTypeSchema (HS.TypeSchema _ typeVars typeExpr) = localEnv $ do
  mapM_ makeTypeVarImplicit typeVars
  convertType typeExpr

-- | Adds the given type variable to the environment and assigns the
--   Coq name @_@ to it.
makeTypeVarImplicit :: HS.TypeVarDecl -> Converter ()
makeTypeVarImplicit (HS.DeclIdent srcSpan ident) = do
  let name = HS.UnQual (HS.Ident ident)
  modifyEnv $ addEntry
    name
    TypeVarEntry
      { entrySrcSpan = srcSpan
      , entryName    = name
      , entryIdent   = G.bare "_"
      }
