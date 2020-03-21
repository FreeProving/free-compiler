-- | This module contains passes for inserting data type, constructor and
--   type synonym declarations as well as function declarations into the
--   environment. Additionally, this pass analyses whether functions are
--   partial or not (since this information is needed for function entries
--   but not encoded into the AST).
--
--   = Specification
--
--   = Preconditions
--
--   The argument and return types and type arguments of function declarations
--   are annotated.
--
--   = Translation
--
--   No changes are made to the declarations.
--
--   = Postconditions
--
--   There are entries for the given declarations in the environment.
--
--   = Error cases
--
--   This pass should not fail. However, the user is informed if a different
--   name is assigned to an entry.

module Compiler.Pass.DefineDeclPass
  ( defineTypeDeclsPass
  , defineFuncDeclsPass
  )
where

import           Control.Monad.Extra            ( anyM )

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Analysis.PartialityAnalysis
import           Compiler.Environment.Entry
import           Compiler.Environment.Renamer
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Converter
import           Compiler.Pass.DependencyAnalysisPass

-- | Inserts all data type declarations and type synonyms in the given strongly
--   connected component into the environment.
defineTypeDeclsPass :: DependencyAwarePass HS.TypeDecl
defineTypeDeclsPass component = do
  mapComponentM_ (mapM defineTypeDecl) component
  return component

-- | Inserts all function declarations in the given strongly connected
--   component into the environment.
--
--   If any function in the component uses a partial function, all of the
--   functions in the component are marked as partial.
defineFuncDeclsPass :: DependencyAwarePass HS.FuncDecl
defineFuncDeclsPass component = do
  anyPartial <- anyM isPartialFuncDecl (unwrapComponent component)
  mapComponentM_ (mapM (defineFuncDecl anyPartial)) component
  return component

-------------------------------------------------------------------------------
-- Type declarations                                                         --
-------------------------------------------------------------------------------

-- | Inserts the given data type (including its constructors) or type synonym
--   declaration into the current environment.
defineTypeDecl :: HS.TypeDecl -> Converter ()
defineTypeDecl (HS.TypeSynDecl srcSpan declIdent typeArgs typeExpr) = do
  _ <- renameAndAddEntry TypeSynEntry
    { entrySrcSpan  = srcSpan
    , entryArity    = length typeArgs
    , entryTypeArgs = map HS.fromDeclIdent typeArgs
    , entryTypeSyn  = typeExpr
    , entryName     = HS.UnQual (HS.Ident (HS.fromDeclIdent declIdent))
    , entryIdent    = undefined -- filled by renamer
    }
  return ()
defineTypeDecl (HS.DataDecl _ (HS.DeclIdent srcSpan ident) typeArgs conDecls) =
  do
    _ <- renameAndAddEntry DataEntry { entrySrcSpan = srcSpan
                                     , entryArity   = length typeArgs
                                     , entryName    = name
                                     , entryIdent   = undefined -- filled by renamer
                                     }
    mapM_ defineConDecl conDecls
 where
  -- | The name of the data type.
  name :: HS.QName
  name = HS.UnQual (HS.Ident ident)

  -- | The type produced by all constructors of the data type.
  returnType :: HS.Type
  returnType = HS.typeConApp srcSpan name (map HS.typeVarDeclToType typeArgs)

  -- | Inserts the given data constructor declaration and its smart constructor
  --   into the current environment.
  defineConDecl :: HS.ConDecl -> Converter ()
  defineConDecl (HS.ConDecl _ (HS.DeclIdent conSrcSpan conIdent) argTypes) = do
    _ <- renameAndAddEntry ConEntry
      { entrySrcSpan    = conSrcSpan
      , entryArity      = length argTypes
      , entryTypeArgs   = map HS.fromDeclIdent typeArgs
      , entryArgTypes   = map Just argTypes
      , entryReturnType = Just returnType
      , entryName       = HS.UnQual (HS.Ident conIdent)
      , entryIdent      = undefined -- filled by renamer
      , entrySmartIdent = undefined -- filled by renamer
      }
    return ()

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

-- | Inserts the given function declaration into the current environment.
--
--   The first argument indicates whether the function is partial or not.
defineFuncDecl :: Bool -> HS.FuncDecl -> Converter ()
defineFuncDecl partial funcDecl = do
  _ <- renameAndAddEntry FuncEntry
    { entrySrcSpan       = HS.funcDeclSrcSpan funcDecl
    , entryArity         = length (HS.funcDeclArgs funcDecl)
    , entryTypeArgs      = map HS.fromDeclIdent (HS.funcDeclTypeArgs funcDecl)
    , entryArgTypes      = map HS.varPatType (HS.funcDeclArgs funcDecl)
    , entryReturnType    = HS.funcDeclReturnType funcDecl
    , entryNeedsFreeArgs = True
    , entryIsPartial     = partial
    , entryName          = HS.funcDeclQName funcDecl
    , entryIdent         = undefined -- filled by renamer
    }
  return ()
