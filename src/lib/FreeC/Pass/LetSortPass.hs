-- | This module contains a compiler pass that brings the bindings of all
--   @let@-expressions in a module into reverse topological order.
--
--   = Examples
--
--   == Example 1
--
--   The bindings of the following @let@-expression are not topologically
--   sorted because the right-hand side of @x@ depends on @y@ but @y@ is
--   defined after @x@.
--
--   > let { x = y; y = 42 } in x
--
--   This pass transforms the @let@-expression above into the following form.
--
--   > let { y = 42; x = y } in x
--
--   == Example 2
--
--   If a @let@-expression contains (mutually) recursive bindings, a fatal
--   error is reported.
--
--   > let { x = y; y = x } in x
--
--   It is not clear at the moment how mutually recursive local variables
--   can be represented when the sharing effect is used.
--
--   = Specification
--
--   == Preconditions
--
--   There are no special requirements.
--
--   == Translations
--
--   Every @let@-expression
--
--   > let { x₁ = e₁; …; xₙ = eₙ } in e
--
--   is transformed into a @let@-expression
--
--   > let { y₁ = f₁; …; yₙ = fₙ } in e
--
--   where @y₁ = f₁, …, yₙ = fₙ@ is a permutation of @x₁ = e₁, …, xₙ = eₙ@
--   such that for every @1 ≤ i ≤ n@ the expression @fᵢ@ contains no free
--   variables @xⱼ@ with @j ≥ i@, i.e., all variables bound by the new
--   @let@-expression are not used before they are declared. If there is no
--   such permutation a fatal error is reported.
--
--   == Postcondition
--
--   The bindings of all @let@-expressions are in reverse topological order and
--   there are no recursive or mutually recursive bindings.
module FreeC.Pass.LetSortPass ( letSortPass ) where

import           FreeC.IR.DependencyGraph
import           FreeC.IR.SrcSpan
import           FreeC.IR.Subterm
import qualified FreeC.IR.Syntax          as IR
import           FreeC.Monad.Reporter
import           FreeC.Pass
import           FreeC.Pretty

-- | A pass that sorts the bindings of @let@-expressions topologically.
letSortPass :: Pass IR.Module IR.Module
letSortPass ast = do
  funcDecls' <- mapM sortFuncDecl (IR.modFuncDecls ast)
  return ast { IR.modFuncDecls = funcDecls' }

-- | Sorts all @let@-expressions on the right-hand side of the given function
--   declaration topologically.
sortFuncDecl :: MonadReporter r => IR.FuncDecl -> r IR.FuncDecl
sortFuncDecl funcDecl = do
  rhs' <- sortExpr (IR.funcDeclRhs funcDecl)
  return funcDecl { IR.funcDeclRhs = rhs' }

-- | Sorts all @let@-expressions in the given expression topologically.
sortExpr :: MonadReporter r => IR.Expr -> r IR.Expr
sortExpr = mapSubtermsM sortLet
 where
  sortLet :: MonadReporter r => IR.Expr -> r IR.Expr
  sortLet (IR.Let srcSpan binds expr exprType) = do
    let components = valueDependencyComponents binds
    binds' <- mapM (fromNonRecursive srcSpan) components
    return (IR.Let srcSpan binds' expr exprType)
  sortLet expr = return expr

  -- | Extracts the single non-recursive @let@-binding from the given strongly
  --   connected component of the dependency graph.
  --
  --   Reports a fatal error with the given source span if the bindings in the
  --   component are recursive.
  fromNonRecursive
    :: MonadReporter r => SrcSpan -> DependencyComponent IR.Bind -> r IR.Bind
  fromNonRecursive _ (NonRecursive bind)     = return bind
  fromNonRecursive srcSpan (Recursive binds) = reportFatal
    $ Message srcSpan Error
    $ "Recursive `let`-bindings are not supported but the bindings for "
    ++ showPretty (map IR.declName binds)
    ++ " form a cycle."
