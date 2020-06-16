-- | Contains functions for renaming Haskell identifiers such that they can be
--   safely used as Coq identifiers.
--
--   Identifiers must not conflict with Coq keywords and must not shadow
--   types, constructors and functions from the Base library.
--
--   Renaming identifiers is also required because in Haskell the scopes for
--   types and functions are separated. Thus it is allowed in Haskell for a
--   data type to have the same name as one of it's constructors. In Coq this
--   would cause a name conflict. Therefore, one of them needs to be renamed.

module FreeC.Environment.Renamer
  ( -- * Predicates
    mustRenameIdent
    -- * Rename identifiers
  , renameIdent
  , renameQualid
    -- * Define and automatically rename identifiers
  , renameEntry
  , renameAndAddEntry
  , renameAndDefineTypeVar
  , renameAndDefineVar
  )
where

import           Control.Monad                  ( when )
import           Data.Char
import           Data.Composition               ( (.:) )
import           Data.Maybe                     ( fromMaybe
                                                , mapMaybe
                                                )
import           Text.Casing
import           Text.RegexPR

import qualified FreeC.Backend.Coq.Base        as Coq.Base
import           FreeC.Backend.Coq.Keywords
import qualified FreeC.Backend.Coq.Syntax      as Coq
import           FreeC.Environment
import           FreeC.Environment.Entry
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Predicates                                                                --
-------------------------------------------------------------------------------

-- | Tests whether the given Coq identifier is a keyword of the Gallina
--   specification language.
--
--   If the identifier conflicts with a keyword, it must be renamed.
isCoqKeyword :: String -> Bool
isCoqKeyword = flip elem coqKeywords

-- | Tests whether the given Coq identifier is part of a command of
--   The Vernacular.
--
--   If the identifier conflicts with a command, it should be renamed to avoid
--   naming conflicts, e.g. the following Haskell data type
--
--   > data Definition = {- ... -}
--
--   would result in a Coq @Inductive@ sentence like
--
--   > Inductive Definition : Type := (* ... *).
--
--   which is not valid.
isVernacularCommand :: String -> Bool
isVernacularCommand = flip elem vernacularCommands

-- | Tests whether the given Coq identifier refers to a predefined type
--   or function without Haskell equivalent from the Coq @Base@ library.
--
--   User defined types or functions with the same name, need to be renamed
--   during the translation to avoid name conflicts. The same is true for Coq
--   types and functions with Haskell equivalent. However, in these cases the
--   identifiers are listed in the 'Environment' already.
isReservedIdent :: String -> Bool
isReservedIdent = flip elem Coq.Base.reservedIdents . Coq.bare

-- | Tests whether the given Coq identifier has been used in the current
--   environment to define a type, constructor, function or variable
--   already.
isUsedIdent :: Environment -> String -> Bool
isUsedIdent = flip elem . mapMaybe Coq.unpackQualid . usedIdents

-- | Tests whether the given Coq identifier must be renamed because it would
--   otherwise conflict with a keyword, reserved or user defined
--   identifier.
mustRenameIdent :: String -> Environment -> Bool
mustRenameIdent ident env =
  isCoqKeyword ident
    || isVernacularCommand ident
    || isReservedIdent ident
    || isUsedIdent env ident

-- | Tests whether the given character is allowed in a Coq identifier.
--
--   The Coq langauge specification also lists `unicode-id-part`s as allowed
--   characters in identifiers and states that those include "non-exhaustively
--   includes symbols for prime letters and subscripts". I have not yet been
--   able to find a way to identify this category of unicode characters in
--   Haskell.
--
--   See <https://coq.inria.fr/refman/language/gallina-specification-language.html#lexical-conventions>
--   for more information.
isAllowedChar :: Char -> Bool
isAllowedChar c = isAllowedFirstChar c || c == '\''

-- | Tests whether the given character is allowed in the first place if a Coq
--   identifier.
--
--   See <https://coq.inria.fr/refman/language/gallina-specification-language.html#lexical-conventions>
--   for more information.
isAllowedFirstChar :: Char -> Bool
isAllowedFirstChar c = isLetter c || isDigit c || c == '_'

-------------------------------------------------------------------------------
-- Rename identifiers                                                        --
-------------------------------------------------------------------------------

-- | Replaces characters that are not allowed in Coq identifiers by
--   underscores.
sanitizeIdent :: String -> String
sanitizeIdent [] = "_"
sanitizeIdent (firstChar : subsequentChars) =
  sanitizeFirstChar firstChar : map sanitizeChar subsequentChars
 where
  -- | Replaces the given character with an underscope if it is not allowed
  --   to occur in the first place of a Coq identifier.
  sanitizeFirstChar :: Char -> Char
  sanitizeFirstChar c | isAllowedFirstChar c = c
                      | otherwise            = '_'

  -- | Replaces the given character with an underscope if it is not allowed
  --   to occur in a Coq identifier.
  sanitizeChar :: Char -> Char
  sanitizeChar c | isAllowedChar c = c
                 | otherwise       = '_'

-- | Renames a Haskell identifier such that it can be savely used in Coq.
--
--   If the identifier has no name conflict, it is return unchanged.
--   If the identifier would cause a name conflict the smallest natural number
--   is appended such that the resulting identifier does not cause a name
--   conflict anymore. If the identifier already ends with a number, the
--   enumeration will start from that number.
renameIdent :: String -> Environment -> String
renameIdent ident env
  | mustRenameIdent ident' env = case matchRegexPR "\\d+$" ident' of
    Just ((number, (prefix, _)), _) -> renameIdent' prefix (read number) env
    Nothing                         -> renameIdent' ident' 0 env
  | otherwise = ident'
 where
  ident' :: String
  ident' = sanitizeIdent ident

-- | Renames an identifier by appending a number. The number is increased
--   until the resulting identifier is available.
renameIdent' :: String -> Int -> Environment -> String
renameIdent' ident n env
  | mustRenameIdent identN env = renameIdent' ident (n + 1) env
  | otherwise                  = identN
 where
  identN :: String
  identN = ident ++ show n

-- | Like 'renameIdent' but the Coq identifier is wrapped in a "Coq.Qualid".
renameQualid :: String -> Environment -> Coq.Qualid
renameQualid = Coq.bare .: renameIdent

-------------------------------------------------------------------------------
-- Define and automatically rename identifiers                               --
-------------------------------------------------------------------------------

-- | Renames the identifier of the given entry such that it does not cause
--   any name conflict in the given environment.
--
--   Returns the renamed entry.
renameEntry :: EnvEntry -> Environment -> EnvEntry
renameEntry entry env
  | isConEntry entry = entry
    { entryIdent      = renameQualid (toCamel (fromHumps ident)) env
    , entrySmartIdent = renameQualid ident env
    }
  | isVarEntry entry || isTypeVarEntry entry = entry
    { entryIdent = renameQualid ident env
    }
  | otherwise = entry { entryIdent = renameQualid ident env }
 where
  ident :: String
  ident = fromMaybe "op" $ IR.identFromQName (entryName entry)

-- | Renames the identifier of the given entry such that it does not cause
--   any name conflict in the current environment and inserts it into the
--   environment.
--
--   The 'entryIdent' and 'entrySmartIdent' fields are filled automatically.
--   The 'entryName' field is used to generate the Coq name.
--
--   If it contains a qualified name, the entry is added to the scope both
--   qualified and unqualified.
--
--   When the entry is a top-level entry (i.e., not a variable or type
--   variable) the qualified name is also added to the environment.
--
--   Returns the renamed entry.
renameAndAddEntry :: EnvEntry -> Converter EnvEntry
renameAndAddEntry entry = do
  -- Generate new Coq identifier.
  entry' <- inEnv $ renameEntry entry
  -- Notify user if the entry was renamed.
  informIfRenamed entry entry'
  -- Associate the entry with its original name.
  modifyEnv (addEntry entry')
  return entry'

-- | Associates the identifier of a user defined Haskell type variable with an
--   automatically generated Coq identifier that does not cause any name
--   conflict in the current environment.
--
--   Returns the generated identifier.
renameAndDefineTypeVar
  :: SrcSpan -- ^ The location of the type variable declaration.
  -> String  -- ^ The name of the type variable.
  -> Converter Coq.Qualid
renameAndDefineTypeVar srcSpan ident = do
  entry <- renameAndAddEntry TypeVarEntry
    { entrySrcSpan = srcSpan
    , entryName    = IR.UnQual (IR.Ident ident)
    , entryIdent   = undefined -- filled by renamer
    }
  return (entryIdent entry)

-- | Associates the identifier of a user defined Haskell variable with an
--   automatically generated Coq identifier that does not cause any name
--   conflict in the current environment.
--
--   Returns the generated identifier.
renameAndDefineVar
  :: SrcSpan       -- ^ The location of the variable declaration.
  -> Bool          -- ^ Whether the variable has not been lifted to the
                   --   free monad.
  -> String        -- ^ The name of the variable.
  -> Maybe IR.Type -- ^ The type of the variable if it is known.
  -> Converter Coq.Qualid
renameAndDefineVar srcSpan isPure ident maybeVarType = do
  entry <- renameAndAddEntry VarEntry { entrySrcSpan = srcSpan
                                      , entryIsPure  = isPure
                                      , entryName = IR.UnQual (IR.Ident ident)
                                      , entryIdent   = undefined -- filled by renamer
                                      , entryType    = maybeVarType
                                      }
  return (entryIdent entry)

-------------------------------------------------------------------------------
-- Error reporting                                                           --
-------------------------------------------------------------------------------

-- | Reports a message if the given entry has been renamed.
informIfRenamed :: EnvEntry -> EnvEntry -> Converter ()
informIfRenamed entry entry' = do
  let topLevel = isTopLevelEntry entry
  when (topLevel && not (IR.isInternalIdent ident) && ident /= ident')
    $  report
    $  Message (entrySrcSpan entry) Info
    $  "Renamed "
    ++ prettyEntryType entry
    ++ " '"
    ++ showPretty (entryName entry)
    ++ "' to '"
    ++ ident'
    ++ "'."
 where
  ident, ident' :: String
  ident = fromMaybe "op" $ IR.identFromQName (entryName entry)
  Just ident'
    | entryHasSmartIdent entry = Coq.unpackQualid (entrySmartIdent entry')
    | otherwise                = Coq.unpackQualid (entryIdent entry')
