-- | This module contains auxiliary functions that are used to translate both
--   recursive and non-recursive Haskell functions to Coq.
module FreeC.Backend.Coq.Converter.FuncDecl.Common
  ( -- * Code Generation
    convertFuncHead
  ) where

import           FreeC.Backend.Coq.Converter.Arg
import           FreeC.Backend.Coq.Converter.Free
import           FreeC.Backend.Coq.Converter.Type
import qualified FreeC.Backend.Coq.Syntax as Coq
import           FreeC.Environment
import qualified FreeC.IR.Syntax as IR
import           FreeC.Monad.Converter

-------------------------------------------------------------------------------
-- Code Generation                                                           --
-------------------------------------------------------------------------------
-- | Converts the name, arguments and return type of a function to Coq.
--
--   This code is shared between the conversion functions for recursive and
--   no recursive functions
--   (see 'Haskell.Backend.Coq.Converter.FuncDecl.NonRec.convertNonRecFuncDecl'
--    and 'Haskell.Backend.Coq.Converter.FuncDecl.Rec.convertRecFuncDecls').
convertFuncHead
  :: IR.FuncDecl -> Converter (Coq.Qualid, [Coq.Binder], Maybe Coq.Term)
convertFuncHead (IR.FuncDecl _ declIdent typeArgs args maybeRetType _) = do
  let name = IR.declIdentName declIdent
  -- Lookup the Coq name of the function.
  Just qualid <- inEnv $ lookupIdent IR.ValueScope name
  -- Generate arguments for free monad if they are not in scope.
  freeArgsNeeded <- inEnv $ needsFreeArgs name
  let freeArgDecls
        | freeArgsNeeded = genericArgDecls Coq.Explicit
        | otherwise = []
  -- Lookup partiality and position of decreasing argument.
  partial <- inEnv $ isPartial name
  -- Convert arguments and return types.
  typeArgs' <- convertTypeVarDecls Coq.Implicit typeArgs
  args' <- mapM convertArg args
  maybeRetType' <- mapM convertType maybeRetType
  return ( qualid
         , freeArgDecls ++ [partialArgDecl | partial] ++ typeArgs' ++ args'
         , maybeRetType'
         )
