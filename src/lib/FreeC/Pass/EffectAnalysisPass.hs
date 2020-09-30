-- | This module contains a compiler pass that updates the effect
--   information of function declaration environment entries.
--
--   = Example
--
--   == Example 1
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
--   == Example 2
--
--   Sharing is also modeled as an effect by the compiler. In contrast to
--   other effects that are introduced by function declarations, the sharing
--   effect is required by a function if it contains @let@-expressions.
--
--   > double :: (Int -> Int) -> Int -> Int
--   > double f x = let x' = f x in x' + x'
--
--   Since the right-hand side contains a @let@-expression the pass updates the
--   environment entry of @double@ such that 'Sharing' is part of
--   'FreeC.Environment.Entry.entryEffects'.
--
--   = Specification
--
--   == Preconditions
--
--   The environment contains entries for all function declarations with no
--   effects in 'FreeC.Environment.Entry.entryEffects'.
--
--   == Translation
--
--   No modifications are made to the AST.
--
--   If a function declaration's right-hand side contains a reference to a
--   function whose entry contains effects, it gets those effects as well.
--
--   If there are mutually recursive function declaration's and one of them
--   gets effects by the rule above, then all need to get those effects.
--
--   == Postconditions
--
--   All occurring effects of functions are added to
--   'FreeC.Environment.Entry.entryEffects' of the corresponding environment
--   entries.
module FreeC.Pass.EffectAnalysisPass ( effectAnalysisPass ) where

import           Data.Maybe                        ( isJust )
import           Data.Set                          ( Set )
import qualified Data.Set                          as Set

import           FreeC.Environment
import qualified FreeC.IR.Base.Prelude             as IR.Prelude
import           FreeC.IR.DependencyGraph          ( unwrapComponent )
import           FreeC.IR.Reference                ( valueRefs )
import           FreeC.IR.Subterm
import qualified FreeC.IR.Syntax                   as IR
import           FreeC.LiftedIR.Effect
import           FreeC.Monad.Converter
import           FreeC.Pass.DependencyAnalysisPass

-- | A compiler pass that updates the effect information of function
--   declaration environment entries.
effectAnalysisPass :: DependencyAwarePass IR.FuncDecl
effectAnalysisPass component = do
  let funcDecls = unwrapComponent component
  effects <- funcComponentEffects funcDecls
  mapM_ (addEffects effects) funcDecls
  return component

-- | Adds the given effects to the environment entry of the given function.
addEffects :: [Effect] -> IR.FuncDecl -> Converter ()
addEffects effects decl = modifyEnv
  $ addEffectsToEntry (IR.funcDeclQName decl) effects

-------------------------------------------------------------------------------
-- Effects of Function Declarations                                          --
-------------------------------------------------------------------------------
-- | Gets all effects that occur in any function of the given strongly
--   connected component of the function dependency graph.
funcComponentEffects :: [IR.FuncDecl] -> Converter [Effect]
funcComponentEffects funcDecls = do
  effects <- Set.unions <$> mapM funcDeclEffects funcDecls
  return (Set.toList effects)

-- | Gets all effects of functions that are used on the right-hand side of the
--   given function or are introduced by subterms such as @let@-expressions.
funcDeclEffects :: IR.FuncDecl -> Converter (Set Effect)
funcDeclEffects funcDecl = do
  refEffects <- Set.unions <$> mapM funcNameEffects (valueRefs funcDecl)
  let rhsEffects = exprEffects (IR.funcDeclRhs funcDecl)
  return (refEffects `Set.union` rhsEffects)

-------------------------------------------------------------------------------
-- Effects of Functions                                                      --
-------------------------------------------------------------------------------
-- | Looks up the effects that are used by the function with the given name.
--
--   If the given name identifies a built-in function such as @undefined@,
--   @error@ or @trace@, the corresponding effect is returned.
funcNameEffects :: IR.QName -> Converter (Set Effect)
funcNameEffects name
  | name == IR.Prelude.undefinedFuncName = return (Set.singleton Partiality)
  | name == IR.Prelude.errorFuncName = return (Set.singleton Partiality)
  | name == IR.Prelude.traceFuncName = return (Set.singleton Tracing)
  | otherwise = Set.fromList <$> inEnv (lookupEffects name)

-------------------------------------------------------------------------------
-- Effects of Expressions                                                    --
-------------------------------------------------------------------------------
-- | Gets the effects that are needed by the given expression or its subterms.
--
--   If an expression contains a @let@-expression, the 'Sharing' effect is
--   required.
exprEffects :: IR.Expr -> Set Effect
exprEffects expr | isJust (findFirstSubterm isLet expr) = Set.singleton Sharing
                 | otherwise = Set.empty
 where
  isLet IR.Let {} = True
  isLet _         = False
