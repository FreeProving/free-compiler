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
  , freshIdent
  , renameAndDefineTypeCon
  , renameAndDefineTypeVar
  , renameAndDefineCon
  , renameAndDefineVar
  )
where

import           Text.RegexPR
import           Text.Casing
import           Data.Maybe                     ( catMaybes )

import           Compiler.Converter.State
import qualified Compiler.Language.Coq.AST     as G
import qualified Compiler.Language.Coq.Base    as CoqBase
import           Compiler.Language.Coq.Keywords
import qualified Compiler.Language.Haskell.SimpleAST
                                               as HS

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
isDefinedIdent :: Environment -> String -> Bool
isDefinedIdent = flip elem . catMaybes . map G.unpackQualid . definedIdents

-- | Tests whether the given Coq identifier must be renamed because it would
--   otherwise conflict with a keyword, reserved or user defined
--   identifier.
mustRenameIdent :: String -> Environment -> Bool
mustRenameIdent ident env =
  isCoqKeyword ident || isReservedIdent ident || isDefinedIdent env ident

-------------------------------------------------------------------------------
-- Rename identifiers                                                        --
-------------------------------------------------------------------------------

-- | Renames a Haskell identifier such that it can be savely used in Coq.
--
--   If the identifier has no name conflict, it is return unchanged.
--   If the identifier would cause a name conflict the smallest natural number
--   is appended such that the resulting identifier does not cause a name
--   conflict anymore. If the identifier already ends with a number, the
--   enumeration will start from that number.
renameIdent :: String -> Environment -> String
renameIdent ident env
  | mustRenameIdent ident env = case matchRegexPR "\\d+$" ident of
    Just ((number, (prefix, _)), _) -> renameIdent' prefix (read number) env
    Nothing                         -> renameIdent' ident 0 env
  | otherwise = ident

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
-- Generate fresh identifiers                                                --
-------------------------------------------------------------------------------

-- | Generates a fresh Coq identifier for the current environment.
freshIdent :: Converter String
freshIdent = do
  ident' <- inEnv $ renameIdent' "_" 0
  modifyEnv $ defineFreshIdent (G.bare ident')
  return ident'

-------------------------------------------------------------------------------
-- Define and automatically rename identifiers                               --
-------------------------------------------------------------------------------

-- | Associates the identifier of a user defined Haskell type constructor with
--   an automatically generated Coq identifier that does not cause any name
--   conflict in the current environment.
--
--   Returns the generated identifier.
renameAndDefineTypeCon :: String -> Converter String
renameAndDefineTypeCon ident = do
  ident' <- inEnv $ renameIdent ident
  modifyEnv $ defineTypeCon (HS.Ident ident) (G.bare ident')
  return ident'

-- | Associates the identifier of a user defined Haskell type variable with an
--   automatically generated Coq identifier that does not cause any name
--   conflict in the current environment.
--
--   Returns the generated identifier.
renameAndDefineTypeVar :: String -> Converter String
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
renameAndDefineCon :: String -> Converter (String, String)
renameAndDefineCon ident = do
  ident'      <- inEnv $ renameIdent (toCamel (fromHumps ident))
  smartIdent' <- inEnv $ renameIdent ident
  modifyEnv $ defineCon (HS.Ident ident) (G.bare ident') (G.bare smartIdent')
  return (ident', smartIdent')

-- | Associates the identifier of a user defined Haskell function or variable
--   with an automatically generated Coq identifier that does not cause any
--   name conflict in the current environment.
--
--   Returns the generated identifier.
renameAndDefineVar :: String -> Converter String
renameAndDefineVar ident = do
  ident' <- inEnv $ renameIdent ident
  modifyEnv $ defineVar (HS.Ident ident) (G.bare ident')
  return ident'
