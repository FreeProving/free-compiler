module Compiler.Haskell.SubtermTests where

import           Test.Hspec
import           Test.QuickCheck

import           Data.Maybe                     ( isJust )

import           Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Haskell.Subterm

import           Compiler.Util.Test

-------------------------------------------------------------------------------
-- Test data                                                                 --
-------------------------------------------------------------------------------

-- | Creates a generator for valid test positions for the given expression.
validTestPos :: HS.Expr -> Gen Pos
validTestPos expr = oneof (map return (pos expr))

-- | Creates a generator for invalid test positions for the given expression
--   (i.e. positions that do not identify a subterm of the given expression).
invalidTestPos :: HS.Expr -> Gen Pos
invalidTestPos expr =
  (arbitrary >>= return . Pos) `suchThat` (not . (`elem` (pos expr)))

-- | Creates a generator for test positions for the given expression.
--
--   The @Bool@ indicates whether the position is valid or not.
testPos :: HS.Expr -> Gen (Pos, Bool)
testPos expr = do
  validPos   <- validTestPos expr
  invalidPos <- invalidTestPos expr
  oneof [return (validPos, True), return (invalidPos, False)]

-------------------------------------------------------------------------------
-- Subterm tests                                                             --
-------------------------------------------------------------------------------

-- | Test group for "Compiler.Haskell.Subterm" tests.
testSubterm :: Spec
testSubterm = describe "Compiler.Haskell.Subterm" $ do
  beforeAll
      (fromReporter $ fromConverter $ parseTestExpr $ unlines
        [ "\\n xs ->"
        , "  if n < 0"
        , "    then undefined"
        , "    else if n == 0"
        , "      then []"
        , "      else case xs of"
        , "        []      -> []"
        , "        x : xs' -> x : take (n - 1) xs'"
        ]
      )
    $ do
        it "selects valid positions successfully" $ \testExpr ->
          property $ forAll (testPos testExpr) $ \(p, valid) ->
            isJust (selectSubterm testExpr p) == valid

        it "replaces valid positions successfully" $ \testExpr ->
          property $ forAll (testPos testExpr) $ \(p, valid) ->
            let testExpr' = (HS.Var NoSrcSpan (HS.Ident "x"))
            in  isJust (replaceSubterm testExpr p testExpr') == valid

        it "produces the input when replacing a subterm with itself"
          $ \testExpr -> property $ forAll (validTestPos testExpr) $ \p ->
              let Just subterm = selectSubterm testExpr p
              in  replaceSubterm testExpr p subterm == Just testExpr

        it "replaces the entire term when replacing at the root position"
          $ \testExpr -> do
              let testExpr' = (HS.Var NoSrcSpan (HS.Ident "x"))
              replaceSubterm testExpr rootPos testExpr'
                `shouldBe` Just testExpr'

        it "finds subterm positions" $ \testExpr -> do
          let isCase (HS.Case _ _ _) = True
              isCase _               = False
          findSubtermPos isCase testExpr `shouldBe` [Pos [1, 3, 3]]

        it "finds subterms" $ \testExpr -> do
          let isVar (HS.Var _ _) = True
              isVar _            = False
          map (\(HS.Var _ name) -> name) (findSubterms isVar testExpr)
            `shouldBe` [ HS.Symbol "<"
                       , HS.Ident "n"
                       , HS.Symbol "=="
                       , HS.Ident "n"
                       , HS.Ident "xs"
                       , HS.Ident "x"
                       , HS.Ident "take"
                       , HS.Symbol "-"
                       , HS.Ident "n"
                       , HS.Ident "xs'"
                       ]
