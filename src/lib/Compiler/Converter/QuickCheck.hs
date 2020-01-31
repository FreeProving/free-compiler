-- | This module contains functions for converting simple QuickCheck properties
--   (i.e. Haskell functions that start with @prop_@) to Coq @Theorem@
--   sentences.

module Compiler.Converter.QuickCheck where

import           Control.Monad.Extra            ( anyM
                                                , findM
                                                , partitionM
                                                )
import           Data.List                      ( isPrefixOf )
import qualified Data.List.NonEmpty            as NonEmpty
import qualified Data.Set                      as Set

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Converter.Expr
import           Compiler.Converter.FuncDecl.Common
import qualified Compiler.Coq.AST              as G
import           Compiler.Environment
import           Compiler.Environment.Entry
import           Compiler.Environment.LookupOrFail
import           Compiler.Environment.Scope
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter

-------------------------------------------------------------------------------
-- QuickCheck import                                                         --
-------------------------------------------------------------------------------

-- | The name of the QuickCheck module.
quickCheckModuleName :: HS.ModName
quickCheckModuleName = "Test.QuickCheck"

-- | Environment for the @Test.QuickCheck@ module.
--
--   Only the @Property@ data type is exported. There are no entries for
--   the supported QuickCheck operators, they are handled directly by the
--   converter.
quickCheckInterface :: ModuleInterface
quickCheckInterface = ModuleInterface
  { interfaceModName = quickCheckModuleName
  , interfaceExports = Set.singleton (TypeScope, propertyQName)
  , interfaceEntries = Set.singleton DataEntry
    { entrySrcSpan = NoSrcSpan
    , entryArity   = 0
    , entryIdent   = G.bare "Prop"
    , entryName    = propertyQName
    }
  }

-- | The name of the @Property@ data type.
propertyName :: HS.Name
propertyName = HS.Ident "Property"

-- | The qualified name of the @Property@ data type.
propertyQName :: HS.QName
propertyQName = HS.Qual quickCheckModuleName propertyName

-------------------------------------------------------------------------------
-- Filter QuickCheck property declarations                                   --
-------------------------------------------------------------------------------

-- | Tests whether the given declaration is a QuickCheck property.
--
--   QuickCheck properties are functions with the prefix `prop_` or which
--   return a value of type `Property`.
isQuickCheckProperty :: HS.FuncDecl -> Converter Bool
isQuickCheckProperty (HS.FuncDecl srcSpan (HS.DeclIdent _ ident) args _)
  | "prop_" `isPrefixOf` ident = return True
  | otherwise = do
    let name = HS.UnQual (HS.Ident ident)
    (HS.TypeSchema _ _ funcType) <- lookupTypeSigOrFail srcSpan name
    (_, returnType)              <- splitFuncType name args funcType
    return (isProperty returnType)
 where
  -- | Tests whether the given type is the `Property`
  isProperty :: HS.Type -> Bool
  isProperty (HS.TypeCon _ name) | name == HS.UnQual propertyName = True
                                 | name == propertyQName          = True
  isProperty _ = False

-- | Tests whether the given strongly connected component of the function
--   dependency graph contains a QuickCheck property.
containsQuickCheckProperty :: DependencyComponent HS.FuncDecl -> Converter Bool
containsQuickCheckProperty (NonRecursive decl) = isQuickCheckProperty decl
containsQuickCheckProperty (Recursive decls) = anyM isQuickCheckProperty decls

-- | Partitions the given list of strongly connected components of the
--   function dependency graph into a list of QuickCheck properties
--   and dependency components that contain no QuickCheck properties.
--
--   Reports a fatal error message if there is there is a (mutually) recursive
--   QuickCheck property in one of the components.
filterQuickCheckProperties
  :: [DependencyComponent HS.FuncDecl]
  -> Converter ([HS.FuncDecl], [DependencyComponent HS.FuncDecl])
filterQuickCheckProperties components = do
  quickCheckIsEnabled <- inEnv isQuickCheckEnabled
  if not quickCheckIsEnabled
    then return ([], components)
    else do
      (quickCheckComponents, otherComponents) <- partitionM
        containsQuickCheckProperty
        components
      quickCheckProperties <- mapM fromNonRecursive quickCheckComponents
      return (quickCheckProperties, otherComponents)
 where
  -- | Extracts the only (non-recursive) QuickCheck property in the given
  --   strongly connected component.
  --
  --   Reports a fatal error message, if the given component contains
  --   recursive function declarations.
  fromNonRecursive :: DependencyComponent HS.FuncDecl -> Converter HS.FuncDecl
  fromNonRecursive (NonRecursive decl ) = return decl
  fromNonRecursive (Recursive    decls) = do
    Just property <- findM isQuickCheckProperty decls
    reportFatal
      $  Message (HS.getSrcSpan property) Error
      $  "QuickCheck properties must not be recursive. "
      ++ "Found (mutually) recursive function declarations: "
      ++ HS.prettyDeclIdents decls

-------------------------------------------------------------------------------
-- Convert QuickCheck property declarations                                  --
-------------------------------------------------------------------------------

-- | Converts the given QuickCheck property to a Coq @Theorem@ with an
--   empty @Proof@.
convertQuickCheckProperty :: HS.FuncDecl -> Converter [G.Sentence]
convertQuickCheckProperty decl = do
  [decl'] <- inferAndInsertTypeSigs [decl]
  defineFuncDecl decl'
  convertQuickCheckProperty' decl'

-- | Implementation of 'convertQuickCheckProperty' that assumes that the
--   type of the given QuickCheck property has been inferred and an entry
--   has been inserted into the environemt.
convertQuickCheckProperty' :: HS.FuncDecl -> Converter [G.Sentence]
convertQuickCheckProperty' (HS.FuncDecl _ declIdent args expr) = localEnv $ do
  let name = HS.UnQual (HS.Ident (HS.fromDeclIdent declIdent))
  (qualid, binders, _) <- convertFuncHead name args
  expr'                <- convertQuickCheckExpr expr
  return
    [ G.AssertionSentence
        (G.Assertion G.Theorem
                     qualid
                     []
                     (G.Forall (NonEmpty.fromList binders) expr')
        )
        G.blankProof
    ]

-------------------------------------------------------------------------------
-- QuickCheck property expressions                                           --
-------------------------------------------------------------------------------

-- | Converts the expression on the right hand side of a QuickCheck property
--   declaration.
convertQuickCheckExpr :: HS.Expr -> Converter G.Term
convertQuickCheckExpr (HS.App _ (HS.App _ (HS.Var _ name) e1) e2)
  | name == HS.UnQual (HS.Symbol "==>")  = convertQuickCheckPrecond e1 e2
  | name == HS.UnQual (HS.Symbol "===")  = convertQuickCheckEq e1 e2
  | name == HS.UnQual (HS.Symbol "=/=")  = convertQuickCheckNeq e1 e2
  | name == HS.UnQual (HS.Symbol ".&&.") = convertQuickCheckConj e1 e2
  | name == HS.UnQual (HS.Symbol ".||.") = convertQuickCheckDisj e1 e2
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
