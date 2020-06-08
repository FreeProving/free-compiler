-- | This module contains passes for inserting data type, constructor and
--   type synonym declarations as well as function declarations into the
--   environment.
--
--   Subsequent passes can still modify entries added by this pass.
--   For example, whether functions are partial or not is determined after
--   this pass (See "FreeC.Pass.PartialityAnalysisPass").
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

module FreeC.Pass.DefineDeclPass
  ( defineTypeDeclsPass
  , defineFuncDeclsPass
  )
where

import           FreeC.Environment.Entry
import           FreeC.Environment.Renamer
import           FreeC.IR.DependencyGraph
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Pass.DependencyAnalysisPass

-- | Inserts all data type declarations and type synonyms in the given strongly
--   connected component into the environment.
defineTypeDeclsPass :: DependencyAwarePass IR.TypeDecl
defineTypeDeclsPass component = do
  mapComponentM_ (mapM defineTypeDecl) component
  return component

-- | Inserts all function declarations in the given strongly connected
--   component into the environment.
--
--   If any function in the component uses a partial function, all of the
--   functions in the component are marked as partial.
defineFuncDeclsPass :: DependencyAwarePass IR.FuncDecl
defineFuncDeclsPass component = do
  mapComponentM_ (mapM defineFuncDecl) component
  return component

-------------------------------------------------------------------------------
-- Type declarations                                                         --
-------------------------------------------------------------------------------

-- | Inserts the given data type (including its constructors) or type synonym
--   declaration into the current environment.
defineTypeDecl :: IR.TypeDecl -> Converter ()
defineTypeDecl (IR.TypeSynDecl srcSpan declIdent typeArgs typeExpr) = do
  _ <- renameAndAddEntry TypeSynEntry
    { entrySrcSpan  = srcSpan
    , entryArity    = length typeArgs
    , entryTypeArgs = map IR.typeVarDeclIdent typeArgs
    , entryTypeSyn  = typeExpr
    , entryName     = IR.declIdentName declIdent
    , entryIdent    = undefined -- filled by renamer
    }
  return ()
defineTypeDecl (IR.DataDecl srcSpan declIdent typeArgs conDecls) = do
  _ <- renameAndAddEntry DataEntry
    { entrySrcSpan   = srcSpan
    , entryArity     = length typeArgs
    , entryName      = IR.declIdentName declIdent
    , entryIdent     = undefined -- filled by renamer
    , entryConsNames = map IR.conDeclQName conDecls
    }
  mapM_ defineConDecl conDecls
 where
  -- | The type produced by all constructors of the data type.
  returnType :: IR.Type
  returnType = IR.typeConApp srcSpan
                             (IR.declIdentName declIdent)
                             (map IR.typeVarDeclToType typeArgs)

  -- | Inserts the given data constructor declaration and its smart constructor
  --   into the current environment.
  defineConDecl :: IR.ConDecl -> Converter ()
  defineConDecl (IR.ConDecl conSrcSpan conDeclIdent argTypes) = do
    _ <- renameAndAddEntry ConEntry
      { entrySrcSpan    = conSrcSpan
      , entryArity      = length argTypes
      , entryTypeArgs   = map IR.typeVarDeclIdent typeArgs
      , entryArgTypes   = map Just argTypes
      , entryReturnType = Just returnType
      , entryName       = IR.declIdentName conDeclIdent
      , entryIdent      = undefined -- filled by renamer
      , entrySmartIdent = undefined -- filled by renamer
      }
    return ()

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

-- | Inserts the given function declaration into the current environment.
defineFuncDecl :: IR.FuncDecl -> Converter ()
defineFuncDecl funcDecl = do
  _ <- renameAndAddEntry FuncEntry
    { entrySrcSpan       = IR.funcDeclSrcSpan funcDecl
    , entryArity         = length (IR.funcDeclArgs funcDecl)
    , entryTypeArgs = map IR.typeVarDeclIdent (IR.funcDeclTypeArgs funcDecl)
    , entryArgTypes      = map IR.varPatType (IR.funcDeclArgs funcDecl)
    , entryReturnType    = IR.funcDeclReturnType funcDecl
    , entryNeedsFreeArgs = True
    , entryIsPartial     = False -- may be updated by partiality analysis pass
    , entryName          = IR.funcDeclQName funcDecl
    , entryIdent         = undefined -- filled by renamer
    }
  return ()
