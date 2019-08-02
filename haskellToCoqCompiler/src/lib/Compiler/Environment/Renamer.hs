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
  , renameAndDefineTypeCon
  , renameAndDefineTypeVar
  , renameAndDefineCon
  , renameAndDefineVar
  , renameAndDefineFunc
  )
where

import           Text.RegexPR
import           Text.Casing
import           Data.Maybe                     ( catMaybes )
import           Data.Char

import           Compiler.Environment
import qualified Compiler.Coq.AST              as G
import qualified Compiler.Coq.Base             as CoqBase
import           Compiler.Coq.Keywords
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Converter

-------------------------------------------------------------------------------
-- Predicates                                                                --
-------------------------------------------------------------------------------

-- | Tests whether the given Coq identifier is a keyword of the Gallina
--   specification language.
--
--   If the identifier conflicts with a keyword, it must be renamed.
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
  isCoqKeyword ident || isReservedIdent ident || isUsedIdent env ident

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

-- | Associates the identifier of a user defined Haskell type constructor with
--   an automatically generated Coq identifier that does not cause any name
--   conflict in the current environment.
--
--   Returns the generated identifier.
renameAndDefineTypeCon
  :: String -- ^ The name of the type constructor.
  -> Int    -- ^ The number of expected type arguments.
  -> Converter String
renameAndDefineTypeCon ident arity = do
  ident' <- inEnv $ renameIdent ident
  modifyEnv $ defineTypeCon (HS.Ident ident) arity (G.bare ident')
  return ident'

-- | Associates the identifier of a user defined Haskell type variable with an
--   automatically generated Coq identifier that does not cause any name
--   conflict in the current environment.
--
--   Returns the generated identifier.
renameAndDefineTypeVar
  :: String -- ^ The name of the type variable.
  -> Converter String
renameAndDefineTypeVar ident = do
  ident' <- inEnv $ renameIdent ident
  modifyEnv $ defineTypeVar (HS.Ident ident) (G.bare ident')
  return ident'

-- | Associates the identifier of a user defined Haskell data constructor
--   with an automatically generated Coq identifier that does not cause any
--   name conflict in the current environment.
--
--   A name for the smart constructor is generated automatically as well.
--   The regular constructor's identifier starts with a lower case letter
--   (i.e. @camelCase@ instead of @PascalCase@).
--
--   Returns the generated identifiers. The first component is the identiier
--   for the regular constructor and the second is the identifier for the
--   smart constructor.
renameAndDefineCon
  :: String          -- ^ The name of the data construtcor.
  -> [Maybe HS.Type] -- ^ The types of the constructor's arguments (if known).
  -> Maybe HS.Type   -- ^ The return type of the constructor (if known).
  -> Converter (String, String)
renameAndDefineCon ident argTypes returnType = do
  ident'      <- inEnv $ renameIdent (toCamel (fromHumps ident))
  smartIdent' <- inEnv $ renameIdent ident
  modifyEnv $ defineCon (HS.Ident ident)
                        (G.bare ident')
                        (G.bare smartIdent')
                        argTypes
                        returnType
  return (ident', smartIdent')

-- | Associates the identifier of a user defined Haskell variable with an
--   automatically generated Coq identifier that does not cause any name
--   conflict in the current environment.
--
--   Returns the generated identifier.
renameAndDefineVar
  :: String -- ^ The name of the variable.
  -> Converter String
renameAndDefineVar ident = do
  ident' <- inEnv $ renameIdent ident
  modifyEnv $ defineVar (HS.Ident ident) (G.bare ident')
  return ident'

-- | Associates the identifier of a user defined Haskell function with an
--   automatically generated Coq identifier that does not cause any name
--   conflict in the current environment.
--
--   Returns the generated identifier.
renameAndDefineFunc
  :: String -- ^ The name of the function.
  -> [Maybe HS.Type] -- ^ The types of the function's arguments (if known).
  -> Maybe HS.Type   -- ^ The return type of the function (if known).
  -> Converter String
renameAndDefineFunc ident argTypes returnType = do
  ident' <- inEnv $ renameIdent ident
  modifyEnv $ defineFunc (HS.Ident ident) (G.bare ident') argTypes returnType
  return ident'
