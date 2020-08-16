-- | This module contains utility functions for tests that have to setup
--   the environment of the converter monad.
module FreeC.Test.Environment
  ( renameAndAddTestEntry
  , defineTestTypeVar
  , defineTestTypeSyn
  , defineTestTypeCon
  , defineTestCon
  , defineTestVar
  , defineTestFunc
  , definePartialTestFunc
  , defineStrictTestFunc
  , definePartialStrictTestFunc
  ) where

import           Data.Maybe                ( fromJust )

import qualified FreeC.Backend.Coq.Syntax  as Coq
import           FreeC.Environment.Entry
import           FreeC.Environment.Renamer
import           FreeC.IR.Reference
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax           as IR
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Test.Parser

-------------------------------------------------------------------------------
-- Common                                                                    --
-------------------------------------------------------------------------------
-- | Adds the given entry to the current environment for testing purposes.
--
--   Returns the Coq identifier assigned to the entry by the renamer.
renameAndAddTestEntry :: EnvEntry -> Converter String
renameAndAddTestEntry entry = do
  entry' <- renameAndAddTestEntry' entry
  return (fromJust (Coq.unpackQualid (entryIdent entry')))

-- | Like 'renameAndAddTestEntry' but does return the renamed entry instead of
--   just its Coq identifier.
renameAndAddTestEntry' :: EnvEntry -> Converter EnvEntry
renameAndAddTestEntry' = renameAndAddEntry

-------------------------------------------------------------------------------
-- Type Variable Entries                                                     --
-------------------------------------------------------------------------------
-- | Adds an entry for a type variable to the current environment for
--   testing purposes.
--
--   Returns the Coq identifier assigned to the type variable.
defineTestTypeVar :: String -> Converter String
defineTestTypeVar nameStr = do
  name <- parseTestQName nameStr
  renameAndAddTestEntry TypeVarEntry
    { entrySrcSpan   = NoSrcSpan
    , entryName      = name
    , entryIdent     = undefined -- filled by renamer
    , entryAgdaIdent = undefined -- filled by renamer
    }

-------------------------------------------------------------------------------
-- Type Synonym Entries                                                      --
-------------------------------------------------------------------------------
-- | Adds an entry for a type synonym to the current environment for
--   testing purposes.
--
--   Returns the Coq identifier assigned to the type synonym.
defineTestTypeSyn :: String -> [ String ] -> String -> Converter String
defineTestTypeSyn nameStr typeArgs typeStr = do
  name <- parseTestQName nameStr
  typeExpr <- parseTestType typeStr
  renameAndAddTestEntry TypeSynEntry
    { entrySrcSpan   = NoSrcSpan
    , entryArity     = length typeArgs
    , entryTypeArgs  = typeArgs
    , entryTypeSyn   = typeExpr
    , entryName      = name
    , entryIdent     = undefined -- filled by renamer
    , entryAgdaIdent = undefined -- filled by renamer
    }

-------------------------------------------------------------------------------
-- Data Type Entries                                                         --
-------------------------------------------------------------------------------
-- | Adds an entry for a type constructor to the current environment for
--   testing purposes.
--
--   Returns the Coq identifier assigned to the type constructor.
defineTestTypeCon :: String -> Int -> [ String ] -> Converter String
defineTestTypeCon nameStr arity consNameStrs = do
  name <- parseTestQName nameStr
  consNames <- mapM parseTestQName consNameStrs
  renameAndAddTestEntry DataEntry
    { entrySrcSpan   = NoSrcSpan
    , entryArity     = arity
    , entryName      = name
    , entryConsNames = consNames
    , entryIdent     = undefined -- filled by renamer
    , entryAgdaIdent = undefined -- filled by renamer
    }

-------------------------------------------------------------------------------
-- Constructor Entries                                                       --
-------------------------------------------------------------------------------
-- | Adds an entry for a data constructor to the current environment for
--   testing purposes.
--
--   The argument and return types are parsed from the given string.
--   Returns the Coq identifier assigned to the data constructor.
defineTestCon :: String -> Int -> String -> Converter (String, String)
defineTestCon nameStr arity typeStr = do
  name <- parseTestQName nameStr
  IR.TypeScheme _ typeArgs typeExpr <- parseExplicitTestTypeScheme typeStr
  let (argTypes, returnType) = IR.splitFuncType typeExpr arity
  entry <- renameAndAddTestEntry' ConEntry
    { entrySrcSpan        = NoSrcSpan
    , entryArity          = arity
    , entryTypeArgs       = map IR.typeVarDeclIdent typeArgs
    , entryArgTypes       = argTypes
    , entryReturnType     = returnType
    , entryName           = name
    , entryIdent          = undefined -- filled by renamer
    , entryAgdaIdent      = undefined -- filled by renamer
    , entrySmartIdent     = undefined -- filled by renamer
    , entryAgdaSmartIdent = undefined -- filled by renamer
    }
  let (Just ident')      = Coq.unpackQualid (entryIdent entry)
      (Just smartIdent') = Coq.unpackQualid (entrySmartIdent entry)
  return (ident', smartIdent')

-------------------------------------------------------------------------------
-- Variable Entries                                                          --
-------------------------------------------------------------------------------
-- | Adds an entry for a local variable to the current environment for
--   testing purposes.
--   Returns the Coq identifier assigned to the variable.
defineTestVar :: String -> Converter String
defineTestVar nameStr = do
  name <- parseTestQName nameStr
  renameAndAddTestEntry VarEntry
    { entrySrcSpan   = NoSrcSpan
    , entryIsPure    = False
    , entryName      = name
    , entryIdent     = undefined -- filled by renamer
    , entryAgdaIdent = undefined -- filled by renamer
    , entryType      = Nothing
    }

-------------------------------------------------------------------------------
-- Function Entries                                                          --
-------------------------------------------------------------------------------
-- | Adds an entry for a function  to the current environment for
--   testing purposes.
--
--   The argument and return types are parsed from the given string.
--   Returns the Coq identifier assigned to the function.
defineTestFunc :: String -> Int -> String -> Converter String
defineTestFunc nameStr arity = defineTestFunc' False (replicate arity False)
  nameStr arity

-- | Like 'defineTestFunc' but the first argument controls whether the
--   defined function is partial or not. The second argument controls the
--   strictness of the function arguments.
defineTestFunc'
  :: Bool -> [ Bool ] -> String -> Int -> String -> Converter String
defineTestFunc' partial areStrict nameStr arity typeStr = do
  name <- parseTestQName nameStr
  IR.TypeScheme _ typeArgs typeExpr <- parseExplicitTestTypeScheme typeStr
  let (argTypes, returnType) = IR.splitFuncType typeExpr arity
  renameAndAddTestEntry FuncEntry
    { entrySrcSpan       = NoSrcSpan
    , entryArity         = arity
    , entryTypeArgs      = map IR.typeVarDeclIdent typeArgs
    , entryArgTypes      = argTypes
    , entryStrictArgs    = areStrict
    , entryReturnType    = returnType
    , entryNeedsFreeArgs = True
    , entryIsPartial     = partial
    , entryName          = name
    , entryIdent         = undefined -- filled by renamer
    , entryAgdaIdent     = undefined -- filled by renamer
    }

-- | Like 'defineTestFunc' but also marks the given function as partial.
--
--   Returns the Coq identifier assigned to the function.
definePartialTestFunc :: String -> Int -> String -> Converter String
definePartialTestFunc nameStr arity = defineTestFunc' True
  (replicate arity False) nameStr arity

-- | Like 'defineTestFunc' but also allows to mark arguments as strict in the
--   second argument.
--
--   Returns the Coq identifier assigned to the function.
defineStrictTestFunc :: String -> [ Bool ] -> String -> Converter String
defineStrictTestFunc nameStr areStrict = defineTestFunc' False areStrict nameStr
  (length areStrict)

-- | Like 'defineTestFunc' but also allows to mark arguments as strict in the
--   second argument and marks the given function as partial.
--
--   Returns the Coq identifier assigned to the function.
definePartialStrictTestFunc :: String -> [ Bool ] -> String -> Converter String
definePartialStrictTestFunc nameStr areStrict = defineTestFunc' True areStrict
  nameStr (length areStrict)

-------------------------------------------------------------------------------
-- Utility Functions                                                         --
-------------------------------------------------------------------------------
-- | Like 'parseTestTypeScheme' but makes sure that all type variables have
--   been introduced explicitly. A common error when writing tests is that the
--   tester forgets that in contrast to Haskell, type variables must
--   be introduced explicitly.
parseExplicitTestTypeScheme :: String -> Converter IR.TypeScheme
parseExplicitTestTypeScheme input = do
  typeScheme <- parseTestTypeScheme input
  if not (null (freeTypeVars typeScheme)) && take 7 input /= "forall."
    then reportFatal
      $ Message NoSrcSpan Internal
      $ "Type signatures in environment entries should not contain any free"
      ++ "type variables, but got `"
      ++ input
      ++ "`. Write `forall. "
      ++ input
      ++ "` if you really intended to do this."
    else return typeScheme
