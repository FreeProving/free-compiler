-- | This module contains passes for inserting data type, constructor and
--   type synonym declarations as well as function declarations into the
--   environment.
--
--   Subsequent passes can still modify entries added by this pass.
--   For example, whether functions are partial or not is determined after
--   this pass (See "Compiler.Pass.PartialityAnalysisPass").
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
--   * The user is informed if a different name is assigned to an entry.

module Compiler.Pass.DefineDeclPass
  ( defineTypeDeclsPass
  , defineFuncDeclsPass
  )
where

import           Compiler.Environment.Entry
import           Compiler.Environment.Renamer
import           Compiler.IR.DependencyGraph
import qualified Compiler.IR.Syntax            as HS
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
  mapComponentM_ (mapM defineFuncDecl) component
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
    , entryTypeArgs = map HS.typeVarDeclIdent typeArgs
    , entryTypeSyn  = typeExpr
    , entryName     = HS.declIdentName declIdent
    , entryIdent    = undefined -- filled by renamer
    }
  return ()
defineTypeDecl (HS.DataDecl srcSpan declIdent typeArgs conDecls) = do
  _ <- renameAndAddEntry DataEntry { entrySrcSpan = srcSpan
                                   , entryArity   = length typeArgs
                                   , entryName    = HS.declIdentName declIdent
                                   , entryIdent   = undefined -- filled by renamer
                                   }
  mapM_ defineConDecl conDecls
 where
  -- | The type produced by all constructors of the data type.
  returnType :: HS.Type
  returnType = HS.typeConApp srcSpan
                             (HS.declIdentName declIdent)
                             (map HS.typeVarDeclToType typeArgs)

  -- | Inserts the given data constructor declaration and its smart constructor
  --   into the current environment.
  defineConDecl :: HS.ConDecl -> Converter ()
  defineConDecl (HS.ConDecl conSrcSpan conDeclIdent argTypes) = do
    _ <- renameAndAddEntry ConEntry
      { entrySrcSpan    = conSrcSpan
      , entryArity      = length argTypes
      , entryTypeArgs   = map HS.typeVarDeclIdent typeArgs
      , entryArgTypes   = map Just argTypes
      , entryReturnType = Just returnType
      , entryName       = HS.declIdentName conDeclIdent
      , entryIdent      = undefined -- filled by renamer
      , entrySmartIdent = undefined -- filled by renamer
      }
    return ()

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

-- | Inserts the given function declaration into the current environment.
defineFuncDecl :: HS.FuncDecl -> Converter ()
defineFuncDecl funcDecl = do
  _ <- renameAndAddEntry FuncEntry
    { entrySrcSpan       = HS.funcDeclSrcSpan funcDecl
    , entryArity         = length (HS.funcDeclArgs funcDecl)
    , entryTypeArgs = map HS.typeVarDeclIdent (HS.funcDeclTypeArgs funcDecl)
    , entryArgTypes      = map HS.varPatType (HS.funcDeclArgs funcDecl)
    , entryReturnType    = HS.funcDeclReturnType funcDecl
    , entryNeedsFreeArgs = True
    , entryIsPartial     = False -- may be updated by partiality analysis pass
    , entryName          = HS.funcDeclQName funcDecl
    , entryIdent         = undefined -- filled by renamer
    }
  return ()
