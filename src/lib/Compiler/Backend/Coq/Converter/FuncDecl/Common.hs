-- | This function contains auxilary functions that are used both to translate
--   recursive and non-recursive Haskell functions to Coq.

module Compiler.Backend.Coq.Converter.FuncDecl.Common
  ( -- * Code generation
    convertFuncHead
  )
where

import           Compiler.Backend.Coq.Converter.Arg
import           Compiler.Backend.Coq.Converter.Free
import           Compiler.Backend.Coq.Converter.Type
import qualified Compiler.Backend.Coq.Syntax   as G
import           Compiler.Environment
import           Compiler.Environment.Scope
import qualified Compiler.IR.Syntax            as HS
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
  let name = HS.declIdentName declIdent
  -- Lookup the Coq name of the function.
  Just qualid    <- inEnv $ lookupIdent ValueScope name
  -- Generate arguments for free monad if they are not in scope.
  freeArgsNeeded <- inEnv $ needsFreeArgs name
  let freeArgDecls | freeArgsNeeded = genericArgDecls G.Explicit
                   | otherwise      = []
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
