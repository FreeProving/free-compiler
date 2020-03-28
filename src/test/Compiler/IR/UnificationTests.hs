module Compiler.IR.UnificationTests where

import           Test.Hspec
import           Test.QuickCheck

import           Control.Monad.Trans.Except     ( runExceptT )

import           Compiler.Environment.Fresh
import qualified Compiler.IR.Syntax            as HS
import           Compiler.IR.Subst
import           Compiler.IR.Unification
import           Compiler.Monad.Converter
import           Compiler.Pretty

import           Compiler.Util.Test

-- | Test group for "Compiler.IR.Unification" tests.
testUnification :: Spec
testUnification = describe "Compiler.IR.Unification.unify" $ do
  context "type variables" $ do
    it "maps variables on the left to variables on the right"
      $ shouldSucceed
      $ fromConverter
      $ do
          a <- parseTestType "a"
          b <- parseTestType "b"
          (a, b) `shouldUnifyTo` b
    it "maps internal variables on the right to variables on the left"
      $ shouldSucceed
      $ fromConverter
      $ do
          a <- parseTestType "a"
          f <- freshTypeVar
          (a, f) `shouldUnifyTo` a
    it "maps internal variables on the left to variables on the right"
      $ shouldSucceed
      $ fromConverter
      $ do
          f <- freshTypeVar
          b <- parseTestType "b"
          (f, b) `shouldUnifyTo` b
    it "maps internal variables on the left to internal variables on the right"
      $ shouldSucceed
      $ fromConverter
      $ do
          f1 <- freshTypeVar
          f2 <- freshTypeVar
          (f1, f2) `shouldUnifyTo` f2
    it "cannot match variable with type containing the variable (occurs check)"
      $ shouldSucceed
      $ fromConverter
      $ do
          t <- parseTestType "a"
          s <- parseTestType "a -> a"
          shouldFailOccursCheck t s
  context "type constructors" $ do
    it "constructors match the same constructor"
      $ shouldSucceed
      $ fromConverter
      $ do
          t <- parseTestType "()"
          (t, t) `shouldUnifyTo` t
    it "arguments of constructors are matched recursively"
      $ shouldSucceed
      $ fromConverter
      $ do
          t <- parseTestType "(a, b)"
          s <- parseTestType "(b, c)"
          (t, s) `shouldUnifyTo` "(c, c)"
    it "constructors do not match other constructors"
      $ shouldSucceed
      $ fromConverter
      $ do
          t <- parseTestType "()"
          s <- parseTestType "Integer"
          shouldFailUnification t s
    it "maps variables on the left to constructors on the right"
      $ shouldSucceed
      $ fromConverter
      $ do
          t <- parseTestType "a"
          s <- parseTestType "()"
          (t, s) `shouldUnifyTo` s
    it "maps variables on the right to constructors on the left"
      $ shouldSucceed
      $ fromConverter
      $ do
          t <- parseTestType "()"
          s <- parseTestType "a"
          (t, s) `shouldUnifyTo` t
  context "type synonyms" $ do
    it "expands nullary type synonyms when necessary"
      $ shouldSucceed
      $ fromConverter
      $ do
          _ <- defineTestTypeCon "Char" 0
          _ <- defineTestTypeSyn "String" [] "[Char]"
          t <- parseTestType "[a]"
          s <- parseTestType "String"
          (t, s) `shouldUnifyTo'` ("[Char]", "String")
    it "expands type synonyms with arguments when necessary"
      $ shouldSucceed
      $ fromConverter
      $ do
          _ <- defineTestTypeSyn "Predicate" ["a"] "a -> Bool"
          t <- parseTestType "Predicate b"
          s <- parseTestType "Integer -> c"
          (t, s)
            `shouldUnifyTo'` ( "Predicate Prelude.Integer"
                             , "Prelude.Integer -> Prelude.Bool"
                             )
    it "can unify two type synonyms with different arity"
      $ shouldSucceed
      $ fromConverter
      $ do
          _ <- defineTestTypeSyn "Foo" ["a"] "a -> Integer"
          _ <- defineTestTypeSyn "Bar" ["a", "b"] "a -> b"
          t <- parseTestType "Foo a"
          s <- parseTestType "Bar b c"
          (t, s) `shouldUnifyTo'` ("Foo b", "Bar b Prelude.Integer")
  context "QuickCheck" $ do
    it "self-unification yields the identity substitution"
      $ property
      $ \typeExpr -> shouldSucceedProperty $ fromConverter $ do
          mgu <- unifyOrFail (HS.typeSrcSpan typeExpr) typeExpr typeExpr
          let typeExpr' = applySubst mgu typeExpr
          return (typeExpr' == typeExpr)


-------------------------------------------------------------------------------
-- Utility functions                                                         --
-------------------------------------------------------------------------------

-- | Unifies the given type expressions and sets the expectation that the
--   both are equal after applying the computed unificator.
shouldUnifyTo :: Pretty a => (HS.Type, HS.Type) -> a -> Converter Expectation
shouldUnifyTo (t, s) expectedOutput =
  shouldUnifyTo' (t, s) (expectedOutput, expectedOutput)

-- | Like 'shouldUnifyTo'' but there are two different expected outputs.
--
--   There can be different outputs for the two type expressions if they
--   contain type synonyms.
shouldUnifyTo'
  :: Pretty a => (HS.Type, HS.Type) -> (a, a) -> Converter Expectation
shouldUnifyTo' (t, s) (ot, os) = do
  t'  <- runPipelineOnType t
  s'  <- runPipelineOnType s
  mgu <- unifyOrFail (HS.typeSrcSpan t') t' s'
  return $ do
    applySubst mgu t' `prettyShouldBe` ot
    applySubst mgu s' `prettyShouldBe` os

-- | Unifies the given type expressions and sets the expectation that the
--   unification fails.
shouldFailUnification :: HS.Type -> HS.Type -> Converter Expectation
shouldFailUnification t s = do
  t'  <- runPipelineOnType t
  s'  <- runPipelineOnType s
  res <- runExceptT $ unify t' s'
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
shouldFailOccursCheck :: HS.Type -> HS.Type -> Converter Expectation
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
