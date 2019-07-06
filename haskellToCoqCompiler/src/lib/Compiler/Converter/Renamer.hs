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

module Compiler.Converter.Renamer
  ( mustRenameIdent
  , renameIdent
  , renameIdent'
  )
where

import           Text.RegexPR

import           Compiler.Converter.State
import           Compiler.Language.Coq.Base    as CoqBase
import           Compiler.Language.Coq.Keywords

-------------------------------------------------------------------------------
-- Predicates                                                                --
-------------------------------------------------------------------------------

-- | Tests whether the given string is a keyword of  the Gallina specification
--   language.
--
--   The converter must rename Haskell identifiers during the conversion to
--   Coq such that no conflict occurs with any keyword.
isCoqKeyword :: String -> Bool
isCoqKeyword = flip elem coqKeywords

-- | Tests whether the given Coq identifier refers to a predefined type
--   or function without Haskell equivalent from the Coq @Base@ library.
--
--   User defined types or functions with the same name, need to be renamed
--   during the translation to avoid name conflicts. The same is true for Coq
--   types and functions with Haskell equivalent. However, in these cases the
--   identifiers are listed in the 'Environment' already.
isReservedIdent :: String -> Bool
isReservedIdent = flip elem CoqBase.reservedIdents

-- | Tests whether the given identifier has been used in the current
--   environment to define a type, constructor, function or variable
--   already.
isDefinedIdent :: Environment -> String -> Bool
isDefinedIdent env ident = ident `elem` definedIdents env

-- | Tests whether the given Coq identifier must be renamed because it would
--   otherwise conflict with a keyword, reserved or user defined
--   identifier.
mustRenameIdent :: Environment -> String -> Bool
mustRenameIdent env ident =
  isCoqKeyword ident || isReservedIdent ident || isDefinedIdent env ident

-------------------------------------------------------------------------------
-- Rename identifiers                                                        --
-------------------------------------------------------------------------------

-- | Renames an identifier such that it can be savely used in Coq.
--
--   If the identifier has no name conflict, it is return unchanged.
--   If the identifier would cause a name conflict the smallest natural number
--   is appended such that the resulting identifier does not cause a name
--   conflict anymore. If the identifier already ends with a number, the
--   enumeration will start from that number.
renameIdent :: Environment -> String -> String
renameIdent env ident
  | mustRenameIdent env ident = case matchRegexPR "\\d+$" ident of
    Just ((number, (prefix, _)), _) -> renameIdent' env prefix (read number)
    Nothing                         -> renameIdent' env ident 0
  | otherwise = ident

-- | Renames an identifier by appending a number. The number is increased
--   until the resulting identifier is available.
renameIdent' :: Environment -> String -> Int -> String
renameIdent' env ident n
  | mustRenameIdent env identN = renameIdent' env ident (n + 1)
  | otherwise                  = identN
 where
  identN :: String
  identN = ident ++ (show n)
