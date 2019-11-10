-- | Contains functions for renaming Haskell identifiers such that they can be
--   savely used as Coq identifiers.
--
--   Identifiers must not conflict with Coq keywords and must not shadow
--   types, constructors and functions from the Base library.
--
--   Renaming identifiers is also required because in Haskell the scopes for
--   types and functions are separated. Thus it is allowed in Haskell for a
--   data type to have the same name as one of it's constructors. In Coq this
--   would cause a name conflict. Therefore, one of them needs to be renamed.

module Compiler.Environment.Renamer
  ( -- * Predicates
    mustRenameIdent
    -- * Rename identifiers
  , renameIdent
    -- * Define and automatically rename identifiers
  , renameEntry
  , renameAndAddEntry
  , renameAndDefineTypeVar
  , renameAndDefineVar
  )
where

import           Control.Monad                  ( when )
import           Data.Char
import           Data.Maybe                     ( catMaybes )
import           Text.Casing
import           Text.RegexPR

import qualified Compiler.Coq.AST              as G
import qualified Compiler.Coq.Base             as CoqBase
import           Compiler.Coq.Keywords
import           Compiler.Environment
import           Compiler.Environment.Entry
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty

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
--   @
--     data Definition = {- ... -}
--   @
--
--   would result in a Coq @Inductive@ sentence like
--
--   @
--     Inductive Definition : Type := (* ... *).
--   @
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
isReservedIdent = flip elem CoqBase.reservedIdents . G.bare

-- | Tests whether the given Coq identifier has been used in the current
--   environment to define a type, constructor, function or variable
--   already.
isUsedIdent :: Environment -> String -> Bool
isUsedIdent = flip elem . catMaybes . map G.unpackQualid . usedIdents

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
  identN = ident ++ (show n)

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
    { entryIdent      = renameIdent (toCamel (fromHumps ident)) env
    , entrySmartIdent = renameIdent ident env
    , entryName       = qualName
    }
  | isVarEntry entry || isTypeVarEntry entry = entry
    { entryIdent = renameIdent ident env
    }
  | otherwise = entry { entryIdent = renameIdent ident env
                      , entryName  = qualName
                      }
 where
  unQualName :: HS.Name
  HS.UnQual (unQualName@(HS.Ident ident)) = entryName entry

  qualName :: HS.QName
  qualName = HS.Qual (envModName env) unQualName

-- | Renames the identifier of the given entry such that it does not cause
--   any name conflict in the current environment and inserts it into the
--   environment.
--
--   The 'entryIdent' and 'entrySmartIdent' fields are filled automatically.
--   The 'entryName' field should contain the unqualified Haskell name.
--   It is used to generate the Coq names.
--
--   When the entry is a top-level entry (i.e., not a variable or type
--   variable) the qualified name is also added to the environment.
--
--   Returns the renamed entry.
renameAndAddEntry :: EnvEntry -> Converter EnvEntry
renameAndAddEntry entry = do
  -- Generate the qualified and unqualified Haskell name.
  modName <- inEnv $ envModName
  let unqualName@(HS.UnQual name) = entryName entry
      qualName                    = HS.Qual modName name
  -- Generate new Coq identifier.
  entry' <- inEnv $ renameEntry entry
  -- Error handling and notifications.
  checkRedefinition unqualName entry'
  informIfRenamed entry entry'
  -- Associate the entry with both the unqualified name.
  -- Top-level entries are also associated with their qualified name.
  modifyEnv $ addEntry unqualName entry'
  when (not (null modName) && isTopLevelEntry entry')
    $ modifyEnv (addEntry qualName entry')
  return entry'

-- | Associates the identifier of a user defined Haskell type variable with an
--   automatically generated Coq identifier that does not cause any name
--   conflict in the current environment.
--
--   Returns the generated identifier.
renameAndDefineTypeVar
  :: SrcSpan -- ^ The location of the type variable declaration.
  -> String  -- ^ The name of the type variable.
  -> Converter String
renameAndDefineTypeVar srcSpan ident = do
  entry <- renameAndAddEntry TypeVarEntry
    { entrySrcSpan = srcSpan
    , entryName    = HS.UnQual (HS.Ident ident)
    , entryIdent   = undefined -- filled by renamer
    }
  return (entryIdent entry)

-- | Associates the identifier of a user defined Haskell variable with an
--   automatically generated Coq identifier that does not cause any name
--   conflict in the current environment.
--
--   Returns the generated identifier.
renameAndDefineVar
  :: SrcSpan -- ^ The location of the variable declaration.
  -> Bool    -- ^ Whether the variable has not been lifted to the free monad.
  -> String  -- ^ The name of the variable.
  -> Converter String
renameAndDefineVar srcSpan isPure ident = do
  entry <- renameAndAddEntry VarEntry
    { entrySrcSpan = srcSpan
    , entryIsPure  = isPure
    , entryName    = HS.UnQual (HS.Ident ident)
    , entryIdent   = undefined -- filled by renamer
    }
  return (entryIdent entry)

-------------------------------------------------------------------------------
-- Error reporting                                                           --
-------------------------------------------------------------------------------

-- | Tests whether there is an entry with the same name in the current
--   scope (not a parent scope) already.
checkRedefinition :: HS.QName -> EnvEntry -> Converter ()
checkRedefinition name entry = do
  localEntry <- inEnv $ existsLocalEntry scope name
  when localEntry $ do
    maybeEntry' <- inEnv $ lookupEntry scope name
    case maybeEntry' of
      Nothing -> return ()
      Just entry' ->
        reportFatal
          $  Message (entrySrcSpan entry) Error
          $  "Multiple declarations of "
          ++ prettyEntryType entry
          ++ " '"
          ++ showPretty name
          ++ "'. Declared at "
          ++ showPretty (entrySrcSpan entry)
          ++ " and "
          ++ showPretty (entrySrcSpan entry')
          ++ "."
 where
  scope :: Scope
  scope = entryScope entry

-- | Reports a message if the given entry has been renamed.
informIfRenamed :: EnvEntry -> EnvEntry -> Converter ()
informIfRenamed entry entry' = do
  let topLevel = isTopLevelEntry entry
  when (topLevel && not (isInternalIdent ident) && ident /= ident')
    $  report
    $  Message (entrySrcSpan entry) Info
    $  "Renamed "
    ++ prettyEntryType entry
    ++ " '"
    ++ ident
    ++ "' to '"
    ++ ident'
    ++ "'."
 where
  ident, ident' :: String
  HS.UnQual (HS.Ident ident) = entryName entry
  ident'                     = entryIdent entry'

-- | Tests whether the given Haskell identifier was generated for internal use.
isInternalIdent :: String -> Bool
isInternalIdent ident = elem '@' ident
