-- | This module contains functions for converting function, constructor and
--   type arguments from Haskell to Coq.

module Compiler.Converter.Arg where

import           Control.Monad                  ( zipWithM )

import           Compiler.Converter.Type
import qualified Compiler.Coq.AST              as G
import           Compiler.Environment
import           Compiler.Environment.Fresh
import           Compiler.Environment.Renamer
import qualified Compiler.Haskell.AST          as HS
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
convertTypeVarDecls explicitness typeVarDecls =
  generateTypeVarDecls explicitness (map HS.fromDeclIdent typeVarDecls)

-- | Generates explicit or implicit Coq binders for the type variables with
--   the given names that are either declared in the head of a data type or
--   type synonym declaration or occur in the type signature of a function.
--
--   The first argument controlls whether the generated binders are explicit
--   (e.g. @(a : Type)@) or implicit (e.g. @{a : Type}@).
generateTypeVarDecls
  :: G.Explicitness    -- ^ Whether to generate an explicit or implit binder.
  -> [HS.TypeVarIdent] -- ^ The names of the type variables to declare.
  -> Converter [G.Binder]
generateTypeVarDecls explicitness idents
  | null idents = return []
  | otherwise = do
    -- TODO detect redefinition
    idents' <- mapM renameAndDefineTypeVar idents
    return [G.typedBinder explicitness (map (G.bare) idents') G.sortType]

-------------------------------------------------------------------------------
-- Function arguments                                                        --
-------------------------------------------------------------------------------

-- | Converts the arguments (variable patterns) of a potentially recursive
--   function with the given types to explicit Coq binders.
--
--   If the type of an argument is not known, it's type will be inferred by
--   Coq.
--
--   If the function is recursive, its decreasing argument (given index),
--   is not lifted.
convertArgs
  :: [HS.VarPat]     -- ^ The function arguments.
  -> [Maybe HS.Type] -- ^ The types of the function arguments.
  -> Maybe Int       -- ^ The position of the decreasing argument.
  -> Converter [G.Binder]
convertArgs args argTypes Nothing = do
  argTypes' <- mapM (mapM convertType) argTypes
  zipWithM convertArg args argTypes'
convertArgs args argTypes (Just index) = do
  bindersBefore <- convertArgs argsBefore argTypesBefore Nothing
  decArgBinder  <- convertDecArg decArg decArgType
  bindersAfter  <- convertArgs argsAfter argTypesAfter Nothing
  return (bindersBefore ++ decArgBinder : bindersAfter)
 where
  (argsBefore    , decArg : argsAfter        ) = splitAt index args
  (argTypesBefore, decArgType : argTypesAfter) = splitAt index argTypes

-- | Converts the argument of a function (a variable pattern) to an explicit
--   Coq binder whose type is inferred by Coq.
convertInferredArg :: HS.VarPat -> Converter G.Binder
convertInferredArg = flip convertArg Nothing

-- | Converts the argument of a function (a variable pattern) with the given
--   type to an explicit Coq binder.
convertTypedArg :: HS.VarPat -> HS.Type -> Converter G.Binder
convertTypedArg arg argType = do
  argType' <- convertType argType
  convertArg arg (Just argType')

-- | Convert the decreasing argument (variable pattern) if a recursive function
--   with the given type to an explicit Coq binder.
--
--   In contrast to a regular typed argument (see 'convertTypedArg'), the
--   decreasing argument is not lifted to the @Free@ monad.
--   It is also registered as a non-monadic value (see 'definePureVar').
convertDecArg :: HS.VarPat -> Maybe HS.Type -> Converter G.Binder
convertDecArg arg argType = do
  argType' <- mapM convertType' argType
  binder   <- convertArg arg argType'
  modifyEnv $ definePureVar (HS.Ident (HS.fromVarPat arg))
  return binder

-- | Converts the argument of a function (a variable pattern) to an explicit
--   Coq binder.
convertArg :: HS.VarPat -> Maybe G.Term -> Converter G.Binder
convertArg (HS.VarPat _ ident) mArgType' = do
  -- TODO detect redefinition.
  ident' <- renameAndDefineVar ident
  generateArgBinder ident' mArgType'

-- | Generates an explicit Coq binder for a function argument with the given
--   name and optional Coq type.
--
--   If no type is provided, it will be inferred by Coq.
generateArgBinder :: String -> Maybe G.Term -> Converter G.Binder
generateArgBinder ident' Nothing =
  return (G.Inferred G.Explicit (G.Ident (G.bare ident')))
generateArgBinder ident' (Just argType') =
  return (G.typedBinder' G.Explicit (G.bare ident') argType')

-- | Converts the argument of an artifically generated function to an explicit
--   Coq binder. A fresh Coq identifier is selected for the argument
--   and returned together with the binder.
convertAnonymousArg :: Maybe HS.Type -> Converter (String, G.Binder)
convertAnonymousArg mArgType = do
  ident'    <- freshCoqIdent freshArgPrefix
  mArgType' <- mapM convertType mArgType
  binder    <- generateArgBinder ident' mArgType'
  return (ident', binder)
