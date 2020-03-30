-- | This module contains functions for generating Coq function, constructor
--   and type arguments from our intermediate representation.

module Compiler.Backend.Coq.Converter.Arg where

import           Compiler.Backend.Coq.Converter.Type
import qualified Compiler.Backend.Coq.Syntax   as G
import           Compiler.Environment.Fresh
import           Compiler.Environment.Renamer
import qualified Compiler.IR.Syntax            as HS
import           Compiler.Monad.Converter

-------------------------------------------------------------------------------
-- Type arguments                                                            --
-------------------------------------------------------------------------------

-- | Converts the declarations of type variables in the head of a data type or
--   type synonym declaration to a Coq binder for a set of explicit or implicit
--   type arguments.
--
--   E.g. the declaration of the type variable @a@ in @data D a = ...@ is
--   translated to the binder @(a : Type)@. If there are multiple type variable
--   declarations as in @data D a b = ...@ they are grouped into a single
--   binder @(a b : Type)@ because we assume all Haskell type variables to be
--   of kind @*@.
--
--   The first argument controlls whether the generated binders are explicit
--   (e.g. @(a : Type)@) or implicit (e.g. @{a : Type}@).
convertTypeVarDecls
  :: G.Explicitness   -- ^ Whether to generate an explicit or implit binder.
  -> [HS.TypeVarDecl] -- ^ The type variable declarations.
  -> Converter [G.Binder]
convertTypeVarDecls explicitness typeVarDecls
  | null typeVarDecls = return []
  | otherwise = do
    idents' <- mapM convertTypeVarDecl typeVarDecls
    return [G.typedBinder explicitness idents' G.sortType]
 where
  -- | TODO
  convertTypeVarDecl :: HS.TypeVarDecl -> Converter G.Qualid
  convertTypeVarDecl (HS.TypeVarDecl srcSpan ident) =
    renameAndDefineTypeVar srcSpan ident

-------------------------------------------------------------------------------
-- Function arguments                                                        --
-------------------------------------------------------------------------------

-- | Converts the given arguments of a function declaration or lambda
--   abstraction to Coq binders.
--
--   If the type of an argument is not annotated, it's type will be inferred
--   by Coq.
--
--   If the function is recursive (i.e., the second argument is not @Nothing@),
--   its decreasing argument (given index) is not lifted.
convertArgs
  :: [HS.VarPat]     -- ^ The function arguments.
  -> Maybe Int       -- ^ The position of the decreasing argument or @Nothing@
                     --   if the function does not decrease on any of its
                     --   arguments.
  -> Converter [G.Binder]
convertArgs args Nothing      = mapM convertArg args
convertArgs args (Just index) = do
  let (argsBefore, decArg : argsAfter) = splitAt index args
  bindersBefore <- convertArgs argsBefore Nothing
  decArgBinder  <- convertPureArg decArg
  bindersAfter  <- convertArgs argsAfter Nothing
  return (bindersBefore ++ decArgBinder : bindersAfter)

-- | Converts the argument of a function (a variable pattern) to an explicit
--   Coq binder.
--
--   If the variable pattern has a type annotation, the generated binder is
--   annotated with the converted type.
convertArg :: HS.VarPat -> Converter G.Binder
convertArg (HS.VarPat srcSpan ident maybeArgType) = do
  ident'        <- renameAndDefineVar srcSpan False ident maybeArgType
  maybeArgType' <- mapM convertType maybeArgType
  generateArgBinder ident' maybeArgType'

-- | Like 'convertArg' but marks the variable as non-monadic.
--
--   If the variable pattern has a type annotation, the generated binder is
--   annotated with the converted type but the type is not lifted to the
--   @Maybe@ monad.
convertPureArg :: HS.VarPat -> Converter G.Binder
convertPureArg (HS.VarPat srcSpan ident maybeArgType) = do
  ident'        <- renameAndDefineVar srcSpan True ident maybeArgType
  maybeArgType' <- mapM convertType' maybeArgType
  generateArgBinder ident' maybeArgType'

-- | Generates an explicit Coq binder for a function argument with the given
--   name and optional Coq type.
--
--   If no type is provided, it will be inferred by Coq.
generateArgBinder :: G.Qualid -> Maybe G.Term -> Converter G.Binder
generateArgBinder ident' Nothing =
  return (G.Inferred G.Explicit (G.Ident ident'))
generateArgBinder ident' (Just argType') =
  return (G.typedBinder' G.Explicit ident' argType')

-- | Converts the argument of an artifically generated function to an explicit
--   Coq binder. A fresh Coq identifier is selected for the argument
--   and returned together with the binder.
convertAnonymousArg :: Maybe HS.Type -> Converter (G.Qualid, G.Binder)
convertAnonymousArg mArgType = do
  ident'    <- freshCoqQualid freshArgPrefix
  mArgType' <- mapM convertType mArgType
  binder    <- generateArgBinder ident' mArgType'
  return (ident', binder)
