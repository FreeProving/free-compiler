-- | This module contains a compiler pass that updates the effect
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
--   > double :: (Int -> Int) -> Int -> Int
--   > double f x = let x' = f x in x' + x'
--
--   Since the right-hand side contains a let expression the pass updates the
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

import           Control.Monad.Extra               ( anyM )

import           FreeC.Environment
import qualified FreeC.IR.Base.Prelude             as IR.Prelude
import           FreeC.IR.DependencyGraph          ( unwrapComponent )
import           FreeC.IR.Reference                ( valueRefs )
import qualified FreeC.IR.Syntax                   as IR
import           FreeC.LiftedIR.Effect
import           FreeC.Monad.Converter
import           FreeC.Pass.DependencyAnalysisPass
import           FreeC.Util.Predicate

-- | A compiler pass that updates the effect information of function
--   declaration environment entries.
effectAnalysisPass :: DependencyAwarePass IR.FuncDecl
effectAnalysisPass component = do
  let funcDecls = unwrapComponent component
  effects <- buildEffectList funcDecls
  mapM_ (addEffects effects) funcDecls
  return component

-- | Returns all effects that occur in the given functions.
buildEffectList :: [IR.FuncDecl] -> Converter [Effect]
buildEffectList funcDecls = do
  anyPartial <- anyM isPartialFuncDecl funcDecls
  anySharing <- (areSharedFuncDecls .||^. containSharedFuncs) funcDecls
  return $ [Partiality | anyPartial] ++ [Sharing | anySharing]

-- | Adds the given effects to the environment entry of the given function.
addEffects :: [Effect] -> IR.FuncDecl -> Converter ()
addEffects effects decl = modifyEnv
  $ addEffectsToEntry (IR.funcDeclQName decl) effects

-------------------------------------------------------------------------------
-- Partiality                                                                --
-------------------------------------------------------------------------------
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
                       | otherwise = inEnv $ hasEffect Partiality name

-------------------------------------------------------------------------------
-- Sharing                                                                   --
-------------------------------------------------------------------------------
-- | Tests whether the given functions contain any let expressions.
areSharedFuncDecls :: [IR.FuncDecl] -> Converter Bool
areSharedFuncDecls = return . any (isLet . IR.funcDeclRhs)

-- | Test whether any of the given functions has the 'Sharing' effect already.
containSharedFuncs :: [IR.FuncDecl] -> Converter Bool
containSharedFuncs = anyM $ anyM (inEnv . hasEffect Sharing) . valueRefs

-- | Tests whether the given expression is or contains a let expression.
isLet :: IR.Expr -> Bool
isLet (IR.App _ lhs rhs _) = isLet lhs || isLet rhs
isLet (IR.TypeAppExpr _ lhs _ _) = isLet lhs
isLet (IR.If _ cond true false _) = isLet cond || isLet true || isLet false
isLet (IR.Case _ expr alts _) = isLet expr || any (isLet . IR.altRhs) alts
isLet (IR.Lambda _ _ rhs _) = isLet rhs
isLet IR.Let {} = True
isLet _ = False
