-- | This module contains functions for converting simple QuickCheck properties
--   (i.e. Haskell functions that start with @prop_@) to Coq @Theorem@
--   sentences.

module Compiler.Converter.QuickCheck where

import           Data.List                      ( find
                                                , isPrefixOf
                                                )

import           Compiler.Analysis.DependencyAnalysis
import qualified Compiler.Coq.AST              as G
import           Compiler.Converter.Expr
import           Compiler.Converter.FuncDecl
import           Compiler.Environment
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter

-------------------------------------------------------------------------------
-- QuickCheck import                                                         --
-------------------------------------------------------------------------------

-- | Enables the translation of QuickCheck properties and imports the relevant
--   symbols into the current environment.
importAndEnableQuickCheck :: Converter ()
importAndEnableQuickCheck = do
  modifyEnv $ enableQuickCheck
  modifyEnv $ defineTypeCon (HS.Ident "Property") 0 (G.bare "Prop")

-------------------------------------------------------------------------------
-- QuickCheck property declarations                                          --
-------------------------------------------------------------------------------

-- | Tests whether the given declaration is a QuickCheck property.
isQuickCheckProperty :: HS.Decl -> Bool
isQuickCheckProperty (HS.FuncDecl _ (HS.DeclIdent _ ident) _ _) =
  "prop_" `isPrefixOf` ident
isQuickCheckProperty _ = False

-- | Like 'convertFuncComponent' but if the translation of QuickCheck
--   properties is enabled, they are passed to 'convertQuickCheckProperty'
--   instead.
--
--   QuickCheck properties are not allowed to be (mutually) recursive.
convertFuncComponentOrQuickCheckProperty
  :: DependencyComponent -> Converter [G.Sentence]
convertFuncComponentOrQuickCheckProperty component@(NonRecursive decl) = do
  quickCheckIsEnabled <- inEnv $ isQuickCheckEnabled
  if quickCheckIsEnabled && isQuickCheckProperty decl
    then convertQuickCheckProperty decl
    else convertFuncComponent component
convertFuncComponentOrQuickCheckProperty component@(Recursive decls) = do
  quickCheckIsEnabled <- inEnv $ isQuickCheckEnabled
  case find isQuickCheckProperty decls of
    Just property | quickCheckIsEnabled ->
      reportFatal
        $ Message (HS.getSrcSpan property) Error
        $ "QuickCheck properties must not be recursive."
    _ -> convertFuncComponent component

-- | Converts the given QuickCheck property to a Coq @Theorem@ with an
--   empty @Proof@.
convertQuickCheckProperty :: HS.Decl -> Converter [G.Sentence]
convertQuickCheckProperty decl@(HS.FuncDecl _ declIdent args expr) = do
  defineFuncDecl decl
  localEnv $ do
    let name = HS.Ident (HS.fromDeclIdent declIdent)
    (qualid, binders, _) <- convertFuncHead name args
    expr'                <- convertQuickCheckExpr expr
    return
      [ G.AssertionSentence (G.Assertion G.Theorem qualid binders expr')
                            (G.ProofAdmitted G.proofPlaceholder)
      ]

-------------------------------------------------------------------------------
-- QuickCheck property expressions                                           --
-------------------------------------------------------------------------------

-- | Converts the expression on the right hand side of a QuickCheck property
--   declaration.
convertQuickCheckExpr :: HS.Expr -> Converter G.Term
convertQuickCheckExpr (HS.App _ (HS.App _ (HS.Var _ name) e1) e2)
  | name == HS.Symbol "==>"  = convertQuickCheckPrecond e1 e2
  | name == HS.Symbol "==="  = convertQuickCheckEq e1 e2
  | name == HS.Symbol "=/="  = convertQuickCheckNeq e1 e2
  | name == HS.Symbol ".&&." = convertQuickCheckConj e1 e2
  | name == HS.Symbol ".||." = convertQuickCheckDisj e1 e2
convertQuickCheckExpr expr = do
  convertQuickCheckBool expr

-- | Converts a boolean expression to a Coq property that states that the
--   expression must evaluate to true.
convertQuickCheckBool :: HS.Expr -> Converter G.Term
convertQuickCheckBool expr = do
  expr' <- convertExpr expr
  true' <- convertExpr (HS.Con NoSrcSpan HS.trueConName)
  return (expr' `G.equals` true')

-- | Converts a QuickCheck precondition to a Coq implication.
convertQuickCheckPrecond :: HS.Expr -> HS.Expr -> Converter G.Term
convertQuickCheckPrecond e1 e2 = do
  e1' <- convertQuickCheckBool e1
  e2' <- convertQuickCheckExpr e2
  return (G.Arrow e1' e2')

-- | Converts the QuickCheck equality @(===)@ to a Coq reflexive equality.
convertQuickCheckEq :: HS.Expr -> HS.Expr -> Converter G.Term
convertQuickCheckEq e1 e2 = do
  e1' <- convertExpr e1
  e2' <- convertExpr e2
  return (G.equals e1' e2')

-- | Converts the QuickCheck equality @(=/=)@ to a Coq reflexive inequality.
convertQuickCheckNeq :: HS.Expr -> HS.Expr -> Converter G.Term
convertQuickCheckNeq e1 e2 = do
  e1' <- convertExpr e1
  e2' <- convertExpr e2
  return (G.notEquals e1' e2')

-- | Converts the QuickCheck conjunction @(.&&.)@ to a Coq conjunction.
convertQuickCheckConj :: HS.Expr -> HS.Expr -> Converter G.Term
convertQuickCheckConj e1 e2 = do
  e1' <- convertQuickCheckExpr e1
  e2' <- convertQuickCheckExpr e2
  return (G.conj e1' e2')

-- | Converts the QuickCheck conjunction @(.||.)@ to a Coq conjunction.
convertQuickCheckDisj :: HS.Expr -> HS.Expr -> Converter G.Term
convertQuickCheckDisj e1 e2 = do
  e1' <- convertQuickCheckExpr e1
  e2' <- convertQuickCheckExpr e2
  return (G.disj e1' e2')
