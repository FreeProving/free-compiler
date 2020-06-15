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
  )
where

import           Data.Maybe                     ( fromJust )

import qualified FreeC.Backend.Coq.Syntax      as Coq
import           FreeC.Environment.Entry
import           FreeC.Environment.Renamer
import           FreeC.IR.Reference
import qualified FreeC.IR.Syntax               as IR
import           FreeC.IR.SrcSpan
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






-- Type variable entries                                                     --






-------------------------------------------------------------------------------







-- | Adds an entry for a type variable to the current environment for






--   testing purposes.






--






--   Returns the Coq identifier assigned to the type variable.






defineTestTypeVar :: String -> Converter String
defineTestTypeVar nameStr = do
  name <- parseTestQName nameStr
  renameAndAddTestEntry TypeVarEntry { entrySrcSpan = NoSrcSpan
                                     , entryName    = name
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
defineTestTypeSyn nameStr typeArgs typeStr = do
  name     <- parseTestQName nameStr
  typeExpr <- parseTestType typeStr
  renameAndAddTestEntry TypeSynEntry { entrySrcSpan  = NoSrcSpan
                                     , entryArity    = length typeArgs
                                     , entryTypeArgs = typeArgs
                                     , entryTypeSyn  = typeExpr
                                     , entryName     = name
                                     , entryIdent    = undefined -- filled by renamer






                                     }

-------------------------------------------------------------------------------






-- Data type entries                                                         --






-------------------------------------------------------------------------------







-- | Adds an entry for a type constructor to the current environment for






--   testing purposes.






--






--   Returns the Coq identifier assigned to the type constructor.






defineTestTypeCon :: String -> Int -> [String] -> Converter String
defineTestTypeCon nameStr arity consNameStrs = do
  name      <- parseTestQName nameStr
  consNames <- mapM parseTestQName consNameStrs
  renameAndAddTestEntry DataEntry { entrySrcSpan   = NoSrcSpan
                                  , entryArity     = arity
                                  , entryName      = name
                                  , entryIdent     = undefined -- filled by renamer
                                  , entryConsNames = consNames
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
defineTestCon nameStr arity typeStr = do
  name                              <- parseTestQName nameStr
  IR.TypeSchema _ typeArgs typeExpr <- parseExplicitTestTypeSchema typeStr
  let (argTypes, returnType) = IR.splitFuncType typeExpr arity
  entry <- renameAndAddTestEntry' ConEntry
    { entrySrcSpan    = NoSrcSpan
    , entryArity      = arity
    , entryTypeArgs   = map IR.typeVarDeclIdent typeArgs
    , entryArgTypes   = map Just argTypes
    , entryReturnType = Just returnType
    , entryName       = name
    , entryIdent      = undefined -- filled by renamer






    , entrySmartIdent = undefined -- filled by renamer






    }
  let (Just ident'     ) = Coq.unpackQualid (entryIdent entry)
      (Just smartIdent') = Coq.unpackQualid (entrySmartIdent entry)
  return (ident', smartIdent')

-------------------------------------------------------------------------------






-- Variable entries                                                          --






-------------------------------------------------------------------------------







-- | Adds an entry for a local variable to the current environment for






--   testing purposes.







--   Returns the Coq identifier assigned to the variable.






defineTestVar :: String -> Converter String
defineTestVar nameStr = do
  name <- parseTestQName nameStr
  renameAndAddTestEntry VarEntry { entrySrcSpan = NoSrcSpan
                                 , entryIsPure  = False
                                 , entryName    = name
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
defineTestFunc' partial nameStr arity typeStr = do
  name                              <- parseTestQName nameStr
  IR.TypeSchema _ typeArgs typeExpr <- parseExplicitTestTypeSchema typeStr
  let (argTypes, returnType) = IR.splitFuncType typeExpr arity
  renameAndAddTestEntry FuncEntry
    { entrySrcSpan       = NoSrcSpan
    , entryArity         = arity
    , entryTypeArgs      = map IR.typeVarDeclIdent typeArgs
    , entryArgTypes      = map Just argTypes
    , entryReturnType    = Just returnType
    , entryNeedsFreeArgs = True
    , entryIsPartial     = partial
    , entryName          = name
    , entryIdent         = undefined -- filled by renamer






    }

-- | Like 'defineTestFunc' but also marks the given function as partial.






--






--   Returns the Coq identifier assigned to the function.






definePartialTestFunc :: String -> Int -> String -> Converter String
definePartialTestFunc = defineTestFunc' True

-------------------------------------------------------------------------------






-- Utility functions                                                         --






-------------------------------------------------------------------------------







-- | Like 'parseTestTypeSchema' but makes sure that all type variables have






--   been introduced explicitly. A common error when writing tests is that the






--   tester forgets that in contrast to Haskell type variables must






--   be introduced explicitly.






parseExplicitTestTypeSchema :: String -> Converter IR.TypeSchema
parseExplicitTestTypeSchema input = do
  typeSchema <- parseTestTypeSchema input
  if not (null (freeTypeVars typeSchema)) && take 7 input /= "forall."
    then
      reportFatal
      $  Message NoSrcSpan Internal
      $  "Type signatures in environment entries should not contain any free"
      ++ "type variables, but got `"
      ++ input
      ++ "`. Write `forall. "
      ++ input
      ++ "` if you really intended to do this."
    else return typeSchema
