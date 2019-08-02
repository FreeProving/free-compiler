-- | This module contains functions for analysising recursive function, e.g. to
--   finding the decreasing argument of a recursive function.

module Compiler.Analysis.RecursionAnalysis where

import           Data.List                      ( nub )
import           Data.Maybe                     ( catMaybes )

import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter

-- | Identifies the decreasing argument of a function with the given right
--   hand side.
--
--   Returns the name of the decreasing argument, the @case@ expressions that
--   match the decreasing argument and a function that replaces the @case@
--   expressions by other expressions.
--
--   TODO verify that all functions in the SCC are decreasing on this argument.
identifyDecArg
  :: HS.Expr -> Converter (HS.Name, [HS.Expr], [HS.Expr] -> HS.Expr)
identifyDecArg rootExpr = do
  case identifyDecArg' rootExpr of
    (Nothing, _, _) ->
      reportFatal
        $ Message (HS.getSrcSpan rootExpr) Error
        $ "Cannot identify decreasing argument."
    (Just decArg, caseExprs, replaceCases) ->
      return (decArg, caseExprs, replaceCases)
 where
  -- | Recursively identifies the decreasing argument (variable matched by the
  --   outermost-case expression).
  identifyDecArg' :: HS.Expr -> (Maybe HS.Name, [HS.Expr], [HS.Expr] -> HS.Expr)
  identifyDecArg' expr@(HS.Case _ (HS.Var _ decArg) _) =
    (Just decArg, [expr], \[expr'] -> expr')
  identifyDecArg' (HS.App srcSpan e1 e2) =
    let (decArg1, cases1, replace1) = identifyDecArg' e1
        (decArg2, cases2, replace2) = identifyDecArg' e2
    in  ( uniqueDecArg [decArg1, decArg2]
        , cases1 ++ cases2
        , \exprs ->
          let e1' = replace1 (take (length cases1) exprs)
              e2' = replace2 (drop (length cases1) exprs)
          in  HS.App srcSpan e1' e2'
        )
  identifyDecArg' (HS.If srcSpan e1 e2 e3) =
    let (decArg1, cases1, replace1) = identifyDecArg' e1
        (decArg2, cases2, replace2) = identifyDecArg' e2
        (decArg3, cases3, replace3) = identifyDecArg' e3
    in  ( uniqueDecArg [decArg1, decArg2, decArg3]
        , cases1 ++ cases2 ++ cases3
        , \exprs ->
          let e1' = replace1 (take (length cases1) exprs)
              e2' =
                replace2 (take (length cases2) (drop (length cases1) exprs))
              e3' = replace3 (drop (length cases1 + length cases2) exprs)
          in  HS.If srcSpan e1' e2' e3'
        )
  identifyDecArg' expr = (Nothing, [], const expr)

  -- | Ensures that all the names of the given list are identical (except for
  --   @Nothing@) and then returns that unique name.
  --
  --   Returns @Nothing@ if there is no such unique name (i.e. because the list
  --   is empty or because there are different names).
  uniqueDecArg :: [Maybe HS.Name] -> Maybe HS.Name
  uniqueDecArg decArgs = case nub (catMaybes decArgs) of
    []       -> Nothing
    [decArg] -> Just decArg
    _        -> Nothing
