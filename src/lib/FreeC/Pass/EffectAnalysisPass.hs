-- | This module contains a compiler pass that updates the partiality
--   information of function declaration environment entries.
--
--   = Example
--
--   The "FreeC.Pass.DefineDeclPass" would add a environment entry whose
--   'FreeC.Environment.Entry.entryEffects' list is empty for the following
--   function declaration.
--
--   > head :: [a] -> a
--   > head xs = case xs of
--   >   []      -> undefined
--   >   x : xs' -> x
--
--   This pass recognizes that the right-hand side of the function declaration
--   for @head@ refers to the built-in function @undefined@. Since @undefined@
--   is partial, @head@ is also partial. Thus, the environment entry of @head@
--   is updated such that 'FreeC.Environment.Entry.entryEffects' contains
--   'Partiality'.
--
--   = Specification
--
--   == Preconditions
--
--   The environment contains entries for all function declarations without
--   'Partiality' in 'FreeC.Environment.Entry.entryEffects'.
--
--   == Translation
--
--   No modifications are made to the AST.
--
--   If a function declaration's right-hand side contains a reference to a
--   function whose entry has been marked as partial (i.e.,
--   'FreeC.Environment.Entry.entryEffects' contains 'Partiality'), it is
--   marked as partial as well.
--
--   If there are mutually recursive function declaration's and one of them
--   needs to be marked as partial by the rule above, then all need to be
--   marked as partial.
--
--   == Postconditions
--
--   'Partiality' is added to 'FreeC.Environment.Entry.entryEffects' of every
--   environment entry if an only if the corresponding function is partial.
module FreeC.Pass.EffectAnalysisPass ( effectAnalysisPass ) where

import           Control.Monad                     ( when )
import           Control.Monad.Extra               ( anyM )

import           FreeC.Environment
import qualified FreeC.IR.Base.Prelude             as IR.Prelude
import           FreeC.IR.DependencyGraph          ( unwrapComponent )
import           FreeC.IR.Reference                ( valueRefs )
import qualified FreeC.IR.Syntax                   as IR
import           FreeC.LiftedIR.Effect
import           FreeC.Monad.Converter
import           FreeC.Pass.DependencyAnalysisPass

-- | A compiler pass that updates the partiality information of function
--   declaration environment entries.
effectAnalysisPass :: DependencyAwarePass IR.FuncDecl
effectAnalysisPass component = do
  let funcDecls = unwrapComponent component
  anyPartial <- anyM isPartialFuncDecl funcDecls
  when anyPartial $ mapM_ markPartial funcDecls
  return component

-- | Tests whether the given function uses a function that has already been
--   marked as partial on its right-hand side.
isPartialFuncDecl :: IR.FuncDecl -> Converter Bool
isPartialFuncDecl decl = anyM isPartialFuncName (valueRefs decl)

-- | Tests whether the function with the given name has been marked as
--   partial.
--
--   The special functions 'IR.undefinedFuncName' and 'IR.errorFuncName'
--   are also partial.
isPartialFuncName :: IR.QName -> Converter Bool
isPartialFuncName name | name == IR.Prelude.undefinedFuncName = return True
                       | name == IR.Prelude.errorFuncName = return True
                       | otherwise = inEnv $ isPartial name

-- | Adds the @Partiality@ effect to the environment entry for the given
--   function declaration.
markPartial :: IR.FuncDecl -> Converter ()
markPartial decl = modifyEnv
  $ addEffectToEntry (IR.funcDeclQName decl) Partiality
