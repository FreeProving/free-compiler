-- | This module contains tests for "FreeC.Pass.PartialityAnalysisPass".
module FreeC.Pass.PartialityAnalysisPassTests
  ( testPartialityAnalysisPass
  ) where

import           Control.Monad.Extra               ( zipWithM_ )
import           Test.Hspec

import           FreeC.Environment
import           FreeC.IR.DependencyGraph
import qualified FreeC.IR.Syntax                   as IR
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Pass.PartialityAnalysisPass
import           FreeC.Pretty
import           FreeC.Test.Environment
import           FreeC.Test.Parser

-------------------------------------------------------------------------------
-- Expectation Setters                                                       --
-------------------------------------------------------------------------------
-- | Parses the function declarations in the given dependency component,
--   runs the 'partialityAnalysisPass' and sets the expectation that there
--   is an environment entry for each function that marks it as partial.
shouldBePartial :: DependencyComponent String -> Converter Expectation
shouldBePartial = shouldBePartialWith
  $ \funcName partial -> if partial
    then return ()
    else expectationFailure
      $ "Expected "
      ++ showPretty funcName
      ++ " to be partial, but it has not been marked as partial."

-- | Like 'shouldBePartial' but sets the expectation that none of the
--   functions are partial.
shouldNotBePartial :: DependencyComponent String -> Converter Expectation
shouldNotBePartial = shouldBePartialWith
  $ \funcName partial -> if not partial
    then return ()
    else expectationFailure
      $ "Expected "
      ++ showPretty funcName
      ++ " to be non-partial, but it has been marked as partial."

-- | Common implementation of 'shouldBePartial' and 'shouldNotBePartial'.
shouldBePartialWith :: (IR.QName -> Bool -> Expectation)
  -> DependencyComponent String -> Converter Expectation
shouldBePartialWith setExpectation inputs = do
  component <- parseTestComponent inputs
  _ <- partialityAnalysisPass component
  let funcNames = map IR.funcDeclQName (unwrapComponent component)
  partials <- mapM (inEnv . isPartial) funcNames
  return (zipWithM_ setExpectation funcNames partials)

-------------------------------------------------------------------------------
-- Tests                                                                     --
-------------------------------------------------------------------------------
-- | Test group for 'partialityAnalysisPass' tests.
testPartialityAnalysisPass :: Spec
testPartialityAnalysisPass = describe "FreeC.Pass.PartialityAnalysisPass"
  $ do
    it "does not classify non-partial functions as partial"
      $ shouldSucceedWith
      $ do
        _ <- defineTestFunc "maybeHead" 1 "forall a. ([]) a -> Maybe a"
        shouldNotBePartial
          $ NonRecursive
          $ "maybeHead xs = case xs of {"
          ++ "  ([])      -> Nothing;"
          ++ "  (:) x xs' -> Just x"
          ++ "}"
    it "recognizes directly partial functions using 'undefined'"
      $ shouldSucceedWith
      $ do
        _ <- defineTestFunc "head" 1 "forall a. ([]) a -> a"
        shouldBePartial
          $ NonRecursive
          $ "head xs = case xs of {"
          ++ "  ([])      -> undefined;"
          ++ "  (:) x xs' -> x"
          ++ "}"
    it "recognizes directly partial functions using 'error'"
      $ shouldSucceedWith
      $ do
        _ <- defineTestFunc "head" 1 "forall a. ([]) a -> a"
        shouldBePartial
          $ NonRecursive
          $ "head xs = case xs of {"
          ++ "  ([])      -> error \"head: empty list\";"
          ++ "  (:) x xs' -> x"
          ++ "}"
    it "recognizes indirectly partial functions"
      $ shouldSucceedWith
      $ do
        _ <- defineTestFunc "map" 2 "forall a b. (a -> b) -> ([]) a -> ([]) b"
        _ <- definePartialTestFunc "head" 1 "forall a. ([]) a -> a"
        _ <- defineTestFunc "heads" 1 "forall a. ([]) a -> ([]) a"
        shouldBePartial $ NonRecursive "heads = map head"
    it "recognizes mutually recursive partial functions"
      $ shouldSucceedWith
      $ do
        _ <- defineTestFunc "map" 2 "forall a b. (a -> b) -> ([]) a -> ([]) b"
        _ <- definePartialTestFunc "head" 1 "forall a. ([]) a -> a"
        _ <- defineTestFunc "pairs" 1 "forall a. ([]) a -> ([]) ((,) a)"
        _ <- defineTestFunc "pairs'" 1 "forall a. a -> ([]) a -> ([]) ((,) a)"
        shouldBePartial
          $ Recursive [ "pairs xys = case xys of {"
                          ++ "    ([])     -> ([]);"
                          ++ "    (:) x ys -> pairs' x ys"
                          ++ "  }"
                      , "pairs' x yxs = case yxs of {"
                          ++ "    ([])     -> undefined;"
                          ++ "    (:) y xs -> (:) ((,) x y) (pairs xs)"
                          ++ "  }"
                      ]
