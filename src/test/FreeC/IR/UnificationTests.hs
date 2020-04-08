-- | This module contains tests for "FreeC.IR.Unification".

module FreeC.IR.UnificationTests where

import           Test.Hspec
import           Test.QuickCheck

import           Control.Monad.Trans.Except     ( runExceptT )

import           FreeC.Environment.Fresh
import qualified FreeC.IR.Syntax               as IR
import           FreeC.IR.Subst
import           FreeC.IR.Unification
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Pretty
import           FreeC.Test.Environment
import           FreeC.Test.Parser
import           FreeC.Test.Arbitrary           ( )

-- | Test group for 'unify' tests.
testUnification :: Spec
testUnification = describe "FreeC.IR.Unification.unify" $ do
  context "type variables" $ do
    it "maps variables on the left to variables on the right"
      $ shouldSucceedWith
      $ do
          a <- parseTestType "a"
          b <- parseTestType "b"
          (a, b) `shouldUnifyTo` b
    it "maps internal variables on the right to variables on the left"
      $ shouldSucceedWith
      $ do
          a <- parseTestType "a"
          f <- freshTypeVar
          (a, f) `shouldUnifyTo` a
    it "maps internal variables on the left to variables on the right"
      $ shouldSucceedWith
      $ do
          f <- freshTypeVar
          b <- parseTestType "b"
          (f, b) `shouldUnifyTo` b
    it "maps internal variables on the left to internal variables on the right"
      $ shouldSucceedWith
      $ do
          f1 <- freshTypeVar
          f2 <- freshTypeVar
          (f1, f2) `shouldUnifyTo` f2
    it "cannot match variable with type containing the variable (occurs check)"
      $ shouldSucceedWith
      $ do
          t <- parseTestType "a"
          s <- parseTestType "a -> a"
          shouldFailOccursCheck t s
  context "type constructors" $ do
    it "constructors match the same constructor" $ shouldSucceedWith $ do
      t <- parseTestType "()"
      (t, t) `shouldUnifyTo` t
    it "arguments of constructors are matched recursively"
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "(,)" 2
          t <- parseTestType "(,) a b"
          s <- parseTestType "(,) b c"
          u <- parseTestType "(,) c c"
          (t, s) `shouldUnifyTo` u
    it "constructors do not match other constructors" $ shouldSucceedWith $ do
      _ <- defineTestTypeCon "()" 0
      _ <- defineTestTypeCon "Integer" 0
      t <- parseTestType "()"
      s <- parseTestType "Integer"
      shouldFailUnification t s
    it "maps variables on the left to constructors on the right"
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "()" 0
          t <- parseTestType "a"
          s <- parseTestType "()"
          (t, s) `shouldUnifyTo` s
    it "maps variables on the right to constructors on the left"
      $ shouldSucceedWith
      $ do
          _ <- defineTestTypeCon "()" 0
          t <- parseTestType "()"
          s <- parseTestType "a"
          (t, s) `shouldUnifyTo` t
  context "type synonyms" $ do
    it "expands nullary type synonyms when necessary" $ shouldSucceedWith $ do
      _  <- defineTestTypeCon "([])" 1
      _  <- defineTestTypeCon "Char" 0
      _  <- defineTestTypeSyn "String" [] "([]) Char"
      t  <- parseTestType "([]) a"
      s  <- parseTestType "String"
      t' <- parseTestType "([]) Char"
      s' <- parseTestType "String"
      (t, s) `shouldUnifyTo'` (t', s')
    it "expands type synonyms with arguments when necessary"
      $ shouldSucceedWith
      $ do
          _  <- defineTestTypeCon "Bool" 0
          _  <- defineTestTypeCon "Integer" 0
          _  <- defineTestTypeSyn "Predicate" ["a"] "a -> Bool"
          t  <- parseTestType "Predicate b"
          s  <- parseTestType "Integer -> c"
          t' <- parseTestType "Predicate Integer"
          s' <- parseTestType "Integer -> Bool"
          (t, s) `shouldUnifyTo'` (t', s')
    it "can unify two type synonyms with different arity"
      $ shouldSucceedWith
      $ do
          _  <- defineTestTypeCon "Integer" 0
          _  <- defineTestTypeSyn "Foo" ["a"] "a -> Integer"
          _  <- defineTestTypeSyn "Bar" ["a", "b"] "a -> b"
          t  <- parseTestType "Foo a"
          s  <- parseTestType "Bar b c"
          t' <- parseTestType "Foo b"
          s' <- parseTestType "Bar b Integer"
          (t, s) `shouldUnifyTo'` (t', s')
  context "QuickCheck" $ do
    it "self-unification yields the identity substitution"
      $ property
      $ \typeExpr -> shouldReturnProperty $ do
          mgu <- unifyOrFail (IR.typeSrcSpan typeExpr) typeExpr typeExpr
          let typeExpr' = applySubst mgu typeExpr
          return (typeExpr' == typeExpr)

-------------------------------------------------------------------------------
-- Expectation setters                                                       --
-------------------------------------------------------------------------------

-- | Unifies the given type expressions and sets the expectation that the
--   both are equal after applying the computed unificator.
shouldUnifyTo :: (IR.Type, IR.Type) -> IR.Type -> Converter Expectation
shouldUnifyTo (t, s) expectedOutput =
  (t, s) `shouldUnifyTo'` (expectedOutput, expectedOutput)

-- | Like 'shouldUnifyTo'' but there are two different expected outputs.
--
--   There can be different outputs for the two type expressions if they
--   contain type synonyms.
shouldUnifyTo'
  :: (IR.Type, IR.Type) -> (IR.Type, IR.Type) -> Converter Expectation
shouldUnifyTo' (t, s) (t', s') = do
  mgu <- unifyOrFail (IR.typeSrcSpan t) t s
  return $ do
    applySubst mgu t' `shouldBe` t'
    applySubst mgu s' `shouldBe` s'

-- | Unifies the given type expressions and sets the expectation that the
--   unification fails.
shouldFailUnification :: IR.Type -> IR.Type -> Converter Expectation
shouldFailUnification t s = do
  res <- runExceptT $ unify t s
  case res of
    Left (UnificationError _ _) -> return (return ())
    Left (OccursCheckFailure _ _) ->
      return
        $  expectationFailure
        $  "Expected unification error, but occurs check failed for `"
        ++ showPretty t
        ++ "` and `"
        ++ showPretty s
        ++ "`."
    Right mgu ->
      return
        $  expectationFailure
        $  "Expected unification error, but found unificator "
        ++ showPretty mgu
        ++ " for `"
        ++ showPretty t
        ++ "` and `"
        ++ showPretty s
        ++ "`."

-- | Unifies the given type expressions and sets the expectation that the
--   occurs check fails.
shouldFailOccursCheck :: IR.Type -> IR.Type -> Converter Expectation
shouldFailOccursCheck t s = do
  res <- runExceptT $ unify t s
  case res of
    Left (OccursCheckFailure _ _) -> return (return ())
    Left (UnificationError _ _) ->
      return
        $  expectationFailure
        $  "Expected occurs check to fail, but got unification error for `"
        ++ showPretty t
        ++ "` and `"
        ++ showPretty s
        ++ "`."
    Right mgu ->
      return
        $  expectationFailure
        $  "Expected occurs check to fail, but found unificator "
        ++ showPretty mgu
        ++ " for `"
        ++ showPretty t
        ++ "` and `"
        ++ showPretty s
        ++ "`."
