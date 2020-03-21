-- | This function contains auxilary functions that are used both to translate
--   recursive and non-recursive Haskell functions to Coq.

module Compiler.Converter.FuncDecl.Common
  ( -- * Code generation
    convertFuncHead
  )
where

import           Compiler.Converter.Arg
import           Compiler.Converter.Free
import           Compiler.Converter.Type
import qualified Compiler.Coq.AST              as G
import           Compiler.Environment
import           Compiler.Environment.Scope
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Converter

-------------------------------------------------------------------------------
-- Code generation                                                           --
-------------------------------------------------------------------------------

-- | Converts the name, arguments and return type of a function to Coq.
--
--   This code is shared between the conversion functions for recursive and
--   no recursive functions (see 'convertNonRecFuncDecl' and
--   'convertRecFuncDecls').
convertFuncHead :: HS.FuncDecl -> Converter (G.Qualid, [G.Binder], Maybe G.Term)
convertFuncHead (HS.FuncDecl _ declIdent typeArgs args _ maybeRetType) = do
  let name = HS.UnQual (HS.Ident (HS.fromDeclIdent declIdent))
  -- Lookup the Coq name of the function.
  Just qualid   <- inEnv $ lookupIdent ValueScope name
  -- Generate arguments for free monad if they are not in scope.
  freeArgDecls  <- generateGenericArgDecls G.Explicit
  -- Lookup partiality and position of decreasing argument.
  partial       <- inEnv $ isPartial name
  decArgIndex   <- inEnv $ lookupDecArgIndex name
  -- Convert arguments and return types.
  typeArgs'     <- convertTypeVarDecls G.Implicit typeArgs
  args'         <- convertArgs args decArgIndex
  maybeRetType' <- mapM convertType maybeRetType
  return
    ( qualid
    , (freeArgDecls ++ [ partialArgDecl | partial ] ++ typeArgs' ++ args')
    , maybeRetType'
    )
