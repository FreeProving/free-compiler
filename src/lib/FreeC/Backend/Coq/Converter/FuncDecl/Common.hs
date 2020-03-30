-- | This function contains auxiliary functions that are used both to translate
--   recursive and non-recursive Haskell functions to Coq.

module FreeC.Backend.Coq.Converter.FuncDecl.Common
  ( -- * Code generation
    convertFuncHead
  )
where

import           FreeC.Backend.Coq.Converter.Arg
import           FreeC.Backend.Coq.Converter.Free
import           FreeC.Backend.Coq.Converter.Type
import qualified FreeC.Backend.Coq.Syntax      as G
import           FreeC.Environment
import           FreeC.Environment.Scope
import qualified FreeC.IR.Syntax               as HS
import           FreeC.Monad.Converter

-------------------------------------------------------------------------------
-- Code generation                                                           --
-------------------------------------------------------------------------------

-- | Converts the name, arguments and return type of a function to Coq.
--
--   This code is shared between the conversion functions for recursive and
--   no recursive functions
--   (see 'Haskell.Backend.Coq.Converter.FuncDecl.NonRec.convertNonRecFuncDecl'
--    and 'Haskell.Backend.Coq.Converter.FuncDecl.Rec.convertRecFuncDecls').
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
    , freeArgDecls ++ [ partialArgDecl | partial ] ++ typeArgs' ++ args'
    , maybeRetType'
    )
