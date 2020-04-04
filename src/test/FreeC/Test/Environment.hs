-- | This module contains utility functions for tests that have to setup
--   the environment of the converter monad.

module FreeC.Test.Environment where

import           Data.Maybe                     ( fromJust
                                                , mapMaybe
                                                )

import qualified FreeC.Backend.Coq.Syntax      as G
import           FreeC.Environment.Entry
import           FreeC.Environment.Renamer
import           FreeC.IR.Reference
import qualified FreeC.IR.Syntax               as HS
import           FreeC.IR.SrcSpan
import           FreeC.Monad.Converter
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
  return (fromJust (G.unpackQualid (entryIdent entry')))

-- | Like 'renameAndAddTestEntry' but does return the renamed entry instead of
--   just its Coq identifier.
renameAndAddTestEntry' :: EnvEntry -> Converter EnvEntry
renameAndAddTestEntry' = renameAndAddEntry

-------------------------------------------------------------------------------
-- Type variable entries                                                     --
-------------------------------------------------------------------------------

-- | Adds an entry for a type variable to the current environment for
--   testing purposes.
--
--   Returns the Coq identifier assigned to the type variable.
defineTestTypeVar :: String -> Converter String
defineTestTypeVar ident = renameAndAddTestEntry TypeVarEntry
  { entrySrcSpan = NoSrcSpan
  , entryName    = HS.UnQual (HS.Ident ident)
  , entryIdent   = undefined -- filled by renamer
  }

-------------------------------------------------------------------------------
-- Type synonym entries                                                      --
-------------------------------------------------------------------------------

-- | Adds an entry for a type synonym to the current environment for
--   testing purposes.
--
--   Returns the Coq identifier assigned to the type synonym.
defineTestTypeSyn :: String -> [String] -> String -> Converter String
defineTestTypeSyn ident typeArgs typeStr = do
  typeExpr <- parseTestType typeStr
  renameAndAddTestEntry TypeSynEntry { entrySrcSpan  = NoSrcSpan
                                     , entryArity    = length typeArgs
                                     , entryTypeArgs = typeArgs
                                     , entryTypeSyn  = typeExpr
                                     , entryName = HS.UnQual (HS.Ident ident)
                                     , entryIdent    = undefined -- filled by renamer
                                     }

-------------------------------------------------------------------------------
-- Data type entries                                                         --
-------------------------------------------------------------------------------

-- | Adds an entry for a type constructor to the current environment for
--   testing purposes.
--
--   Returns the Coq identifier assigned to the type constructor.
defineTestTypeCon :: String -> Int -> Converter String
defineTestTypeCon ident arity = renameAndAddTestEntry DataEntry
  { entrySrcSpan = NoSrcSpan
  , entryArity   = arity
  , entryName    = HS.UnQual (HS.Ident ident)
  , entryIdent   = undefined -- filled by renamer
  }

-------------------------------------------------------------------------------
-- Constructor entries                                                       --
-------------------------------------------------------------------------------

-- | Adds an entry for a data constructor to the current environment for
--   testing purposes.
--
--   The argument and return types are parsed from the given string.
--   Returns the Coq identifier assigned to the data constructor.
defineTestCon :: String -> Int -> String -> Converter (String, String)
defineTestCon ident arity typeStr = do
  typeExpr <- parseTestType typeStr
  let (argTypes, returnType) = HS.splitFuncType typeExpr arity
  entry <- renameAndAddTestEntry' ConEntry
    { entrySrcSpan    = NoSrcSpan
    , entryArity      = arity
    , entryTypeArgs   = mapMaybe HS.identFromQName (freeTypeVars returnType)
    , entryArgTypes   = map Just argTypes
    , entryReturnType = Just returnType
    , entryName       = HS.UnQual (HS.Ident ident)
    , entryIdent      = undefined -- filled by renamer
    , entrySmartIdent = undefined -- filled by renamer
    }
  let (Just ident'     ) = G.unpackQualid (entryIdent entry)
      (Just smartIdent') = G.unpackQualid (entrySmartIdent entry)
  return (ident', smartIdent')

-------------------------------------------------------------------------------
-- Variable entries                                                          --
-------------------------------------------------------------------------------

-- | Adds an entry for a local variable to the current environment for
--   testing purposes.

--   Returns the Coq identifier assigned to the variable.
defineTestVar :: String -> Converter String
defineTestVar ident = renameAndAddTestEntry VarEntry
  { entrySrcSpan = NoSrcSpan
  , entryIsPure  = False
  , entryName    = HS.UnQual (HS.Ident ident)
  , entryIdent   = undefined -- filled by renamer
  , entryType    = Nothing
  }

-------------------------------------------------------------------------------
-- Function entries                                                          --
-------------------------------------------------------------------------------

-- | Adds an entry for a function  to the current environment for
--   testing purposes.
--
--   The argument and return types are parsed from the given string.
--   Returns the Coq identifier assigned to the function.
defineTestFunc :: String -> Int -> String -> Converter String
defineTestFunc = defineTestFunc' False

-- | Like 'defineTestFunc' but the first argument controls whether the
--   defined function is partial or not.
defineTestFunc' :: Bool -> String -> Int -> String -> Converter String
defineTestFunc' partial ident arity typeStr = do
  HS.TypeSchema _ typeArgs typeExpr <- parseTestTypeSchema typeStr
  let (argTypes, returnType) = HS.splitFuncType typeExpr arity
  renameAndAddTestEntry FuncEntry
    { entrySrcSpan       = NoSrcSpan
    , entryArity         = arity
    , entryTypeArgs      = map HS.typeVarDeclIdent typeArgs
    , entryArgTypes      = map Just argTypes
    , entryReturnType    = Just returnType
    , entryNeedsFreeArgs = True
    , entryIsPartial     = partial
    , entryName          = HS.UnQual (HS.Ident ident)
    , entryIdent         = undefined -- filled by renamer
    }

-- | Like 'defineTestFunc' but also marks the given function as partial.
--
--   Returns the Coq identifier assigned to the function.
definePartialTestFunc :: String -> Int -> String -> Converter String
definePartialTestFunc = defineTestFunc' True
