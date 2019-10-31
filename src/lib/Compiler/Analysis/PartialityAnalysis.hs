-- | This module contains functions for testing  whether a function
--   declaration is partial (i.e., needs a instance of the @Partial@
--   type class when translated to Coq).

module Compiler.Analysis.PartialityAnalysis
  ( isPartialFuncDecl
  , isPartialExpr
  )
where

import           Compiler.Environment
import           Compiler.Environment.Renamer
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Monad.Converter

-- | Tests whether the given function uses a partial function on its
--   right-hand side.
isPartialFuncDecl :: HS.FuncDecl -> Converter Bool
isPartialFuncDecl (HS.FuncDecl _ _ args expr) = localEnv $ do
  mapM_ shadowVar args
  isPartialExpr expr

-- | Tests whether the given expression uses a partial function.
isPartialExpr :: HS.Expr -> Converter Bool
isPartialExpr (HS.Con _ _    ) = return False
isPartialExpr (HS.Var _ name ) = inEnv $ isPartial name
isPartialExpr (HS.App _ e1 e2) = do
  p1 <- isPartialExpr e1
  p2 <- isPartialExpr e2
  return (p1 || p2)
isPartialExpr (HS.If _ e1 e2 e3) = do
  p1 <- isPartialExpr e1
  p2 <- isPartialExpr e2
  p3 <- isPartialExpr e3
  return (p1 || p2 || p3)
isPartialExpr (HS.Case _ expr alts) = do
  partialExpr <- isPartialExpr expr
  partialArgs <- mapM isPartialAlt alts
  return (foldr (||) partialExpr partialArgs)
isPartialExpr (HS.Undefined _       ) = return True
isPartialExpr (HS.ErrorExpr  _ _    ) = return True
isPartialExpr (HS.IntLiteral _ _    ) = return False
isPartialExpr (HS.Lambda _ args expr) = localEnv $ do
  mapM_ shadowVar args
  isPartialExpr expr

-- | Tests whether the given alternative of a case expression uses a partial
--   function on its right-hand side.
isPartialAlt :: HS.Alt -> Converter Bool
isPartialAlt (HS.Alt _ _ varPats expr) = localEnv $ do
  mapM_ shadowVar varPats
  isPartialExpr expr

-- | Inserts entries for the given variable entry into the current
--   environment such that function entries with the same name are
--   shadowed.
shadowVar :: HS.VarPat -> Converter ()
shadowVar (HS.VarPat srcSpan ident) = do
  _ <- renameAndDefineVar srcSpan False ident
  return ()
