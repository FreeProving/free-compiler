-- | This module contains the new implementation of the converter from
--   Haskell to Coq using the @Free@ monad.
--
--   TODO rename to @Compiler.Converter@

module Compiler.MyConverter where

import           Compiler.Util.Data.List.NonEmpty
import           Compiler.Converter.State
import qualified Compiler.Language.Coq.AST     as G
import qualified Compiler.Language.Coq.Base    as CoqBase
import qualified Compiler.Language.Haskell.SimpleAST
                                               as HS
import           Compiler.Pretty
import           Compiler.Reporter
import           Compiler.SrcSpan

-- | Initially the environment contains the predefined functions, data types
--   and their constructors from the Coq Base library that accompanies this
--   compiler.
defaultEnvironment :: Environment
defaultEnvironment = CoqBase.predefine emptyEnvironment

-------------------------------------------------------------------------------
-- Type expressions                                                          --
-------------------------------------------------------------------------------

-- | Converts a Haskell type to Coq, lifting it into the @Free@ monad.
--
--   This is the implementation of the @†@ translation for types.
convertType :: HS.Type -> Converter G.Term
convertType t = do
  t' <- convertType' t
  return (genericApply CoqBase.free [t'])

-- | Converts a Haskell type to Coq.
--
--   In contrast to 'convertType', the type itself is not lifted into the
--   @Free@ moand. Only the argument and return types of contained function
--   type constructors are lifted recursivly.
--
--   This is the implementation of the @*@ translation for types.
convertType' :: HS.Type -> Converter G.Term
convertType' (HS.TypeVar srcSpan ident) = do
  mQualid <- inEnv $ lookupTypeVar (HS.Ident ident)
  case mQualid of
    Nothing     -> unknownTypeVarError srcSpan ident
    Just qualid -> return (G.Qualid qualid)
convertType' (HS.TypeCon srcSpan name) = do
  mQualid <- inEnv $ lookupTypeCon name
  case mQualid of
    Nothing     -> unknownTypeConError srcSpan name
    Just qualid -> return (genericApply qualid [])
convertType' (HS.TypeApp _ t1 t2) = do
  t1' <- convertType' t1
  t2' <- convertType' t2
  return (G.app t1' [t2'])
convertType' (HS.TypeFunc _ t1 t2) = do
  t1' <- convertType t1
  t2' <- convertType t2
  return (G.Arrow t1' t2')

-------------------------------------------------------------------------------
-- Utility functions                                                         --
-------------------------------------------------------------------------------

-- | Smart constructor for the application of a Coq function or (type)
--   constructor that requires the parameters for the @Free@ monad.
genericApply :: G.Qualid -> [G.Term] -> G.Term
genericApply func args = G.app (G.Qualid func) (genericArgs ++ args)
  where genericArgs = map (G.Qualid . fst) CoqBase.freeArgs

-------------------------------------------------------------------------------
-- Error reporting                                                           --
-------------------------------------------------------------------------------

-- | Reports a fatal error message when an unknown type constructor is
--   encountered.
unknownTypeConError :: SrcSpan -> HS.Name -> Converter a
unknownTypeConError srcSpan name = liftReporter $ reportFatal $ Message
  (Just srcSpan)
  Error
  ("Unknown type constructor: " ++ showPretty name)

-- | Reports a fatal error message when an unknown type variable is
--   encountered.
--
--   This could happen if a type variable is used in a data constructor
--   that was not declaraed in the data type declaration's head.
unknownTypeVarError :: SrcSpan -> HS.TypeVarIdent -> Converter a
unknownTypeVarError srcSpan ident = liftReporter $ reportFatal $ Message
  (Just srcSpan)
  Error
  ("Unknown type variable: " ++ ident)
