-- | This module contains a compiler pass that updates the partiality
--   information of function declaration environment entries.
--
--   = Example
--
--   The "FreeC.Pass.DefineDeclPass" would add a environment entry whose
--   'entryIsPartial' flag is set to @False@ for the following function
--   declaration.
--
--   @
--   head :: [a] -> a
--   head xs = case xs of
--     []      -> undefined
--     x : xs' -> x
--   @
--
--   This pass recognizes that the right-hand side of the function declaration
--   for @head@ refers to the built-in function @undefined@. Since @undefined@
--   is partial, @head@ is also partial. Thus, the environment entry of @head@
--   is updated such that 'entryIsPartial' is set to @True@.
--
--   = Specification
--
--   == Preconditions
--
--   The environment contains entries for all function declarations whose
--   'entryIsPartial' flag is set to @False@.
--
--   == Translation
--
--   No modifications are made to the AST.
--
--   If a function declaration's right-hand side contains a reference to a
--   function whose entry has been marked as partial (i.e., 'entryIsPartial'
--   is set to @True@), it is marked as partial as well.
--
--   If there are mutually recursive function declaration's and one of them
--   needs to be marked as partial by the rule above, then all need to be
--   marked as partial.
--
--   == Postconditions
--
--   The 'entryIsPartial' flag of every environment entry is set to @True@ if
--   an only if the corresponding function is partial.

module FreeC.Pass.PartialityAnalysisPass
  ( partialityAnalysisPass
  )
where

import           Control.Monad                  ( when )
import           Control.Monad.Extra            ( anyM )

import           FreeC.Environment
import           FreeC.Environment.Entry
import           FreeC.Environment.Scope
import           FreeC.IR.DependencyGraph       ( unwrapComponent )
import           FreeC.IR.Reference             ( valueRefs )
import qualified FreeC.IR.Syntax               as HS
import           FreeC.Monad.Converter
import           FreeC.Pass.DependencyAnalysisPass

-- | A compiler pass that updates the partiality information of function
--   declaration environment entries.
partialityAnalysisPass :: DependencyAwarePass HS.FuncDecl
partialityAnalysisPass component = do
  let funcDecls = unwrapComponent component
  anyPartial <- anyM isPartialFuncDecl funcDecls
  when anyPartial $ mapM_ markPartial funcDecls
  return component

-- | Tests whether the given function uses a function that has already been
--   marked as partial on its right-hand side.
isPartialFuncDecl :: HS.FuncDecl -> Converter Bool
isPartialFuncDecl decl = anyM isPartialFuncName (valueRefs decl)

-- | Tests whether the function with the given name has been marked as
--   partial.
--
--   The special functions 'HS.undefinedFuncName' and 'HS.errorFuncName'
--   are also partial.
isPartialFuncName :: HS.QName -> Converter Bool
isPartialFuncName name | name == HS.undefinedFuncName = return True
                       | name == HS.errorFuncName     = return True
                       | otherwise                    = inEnv $ isPartial name

-- | Sets the 'entryIsPartial' flag of the environment entry for the given
--   function delcaration to @True@.
markPartial :: HS.FuncDecl -> Converter ()
markPartial decl = do
  Just entry <- inEnv $ lookupEntry ValueScope (HS.funcDeclQName decl)
  modifyEnv $ addEntry entry { entryIsPartial = True }
