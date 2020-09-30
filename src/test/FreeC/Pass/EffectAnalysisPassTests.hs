-- | This module contains tests for "FreeC.Pass.EffectAnalysisPassTests".
module FreeC.Pass.EffectAnalysisPassTests ( testEffectAnalysisPass ) where

import           Control.Monad.Extra           ( zipWithM_ )
import           Test.Hspec

import           FreeC.Environment
import           FreeC.IR.DependencyGraph
import qualified FreeC.IR.Syntax               as IR
import           FreeC.LiftedIR.Effect
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Pass.EffectAnalysisPass
import           FreeC.Pretty
import           FreeC.Test.Environment
import           FreeC.Test.Parser

-------------------------------------------------------------------------------
-- Expectation Setters                                                       --
-------------------------------------------------------------------------------
-- | Parses the function declarations in the given dependency component,
--   runs the 'effectAnalysisPass' and sets the expectation that there
--   is an environment entry for each function that contains the given effect
--   in its effect set.
shouldHaveEffect
  :: Effect -> DependencyComponent String -> Converter Expectation
shouldHaveEffect effect = withEffects $ \funcName effects -> if effect
  `elem` effects
  then return ()
  else expectationFailure
    $ "Expected "
    ++ showPretty funcName
    ++ " to have effect "
    ++ show effect
    ++ ", but it only has effects: "
    ++ show effects
    ++ "."

-- | Like 'shouldHaveEffect' but sets the expectation that none of the
--   functions have the given effect.
shouldNotHaveEffect
  :: Effect -> DependencyComponent String -> Converter Expectation
shouldNotHaveEffect effect = withEffects $ \funcName effects -> if effect
  `notElem` effects
  then return ()
  else expectationFailure
    $ "Expected "
    ++ showPretty funcName
    ++ " to not have effect "
    ++ show effect
    ++ ", but it has effects: "
    ++ show effects
    ++ "."

-- | Common implementation of 'shouldHaveEffect' and 'shouldNotHaveEffect'.
withEffects :: (IR.QName -> [Effect] -> Expectation)
            -> DependencyComponent String
            -> Converter Expectation
withEffects setExpectation inputs = do
  component <- parseTestComponent inputs
  _ <- effectAnalysisPass component
  let funcNames = map IR.funcDeclQName (unwrapComponent component)
  effects <- mapM (inEnv . lookupEffects) funcNames
  return (zipWithM_ setExpectation funcNames effects)

-------------------------------------------------------------------------------
-- Tests                                                                     --
-------------------------------------------------------------------------------
-- | Test group for 'Partiality' effect of 'effectAnalysisPass' tests.
testEffectAnalysisPass :: Spec
testEffectAnalysisPass = describe "FreeC.Pass.EffectAnalysisPass" $ do
  it "does not classify non-partial functions as partial"
    $ shouldSucceedWith
    $ do
      _ <- defineTestFunc "maybeHead" 1 "forall a. ([]) a -> Maybe a"
      shouldNotHaveEffect Partiality
        $ NonRecursive
        $ "maybeHead xs = case xs of {"
        ++ "  ([])      -> Nothing;"
        ++ "  (:) x xs' -> Just x"
        ++ "}"
  it "recognizes directly partial functions using 'undefined'"
    $ shouldSucceedWith
    $ do
      _ <- defineTestFunc "head" 1 "forall a. ([]) a -> a"
      shouldHaveEffect Partiality
        $ NonRecursive
        $ "head xs = case xs of {"
        ++ "  ([])      -> undefined;"
        ++ "  (:) x xs' -> x"
        ++ "}"
  it "recognizes directly partial functions using 'error'"
    $ shouldSucceedWith
    $ do
      _ <- defineTestFunc "head" 1 "forall a. ([]) a -> a"
      shouldHaveEffect Partiality
        $ NonRecursive
        $ "head xs = case xs of {"
        ++ "  ([])      -> error \"head: empty list\";"
        ++ "  (:) x xs' -> x"
        ++ "}"
  it "recognizes indirectly partial functions" $ shouldSucceedWith $ do
    _ <- defineTestFunc "map" 2 "forall a b. (a -> b) -> ([]) a -> ([]) b"
    _ <- definePartialTestFunc "head" 1 "forall a. ([]) a -> a"
    _ <- defineTestFunc "heads" 1 "forall a. ([]) a -> ([]) a"
    shouldHaveEffect Partiality $ NonRecursive "heads = map head"
  it "recognizes mutually recursive partial functions" $ shouldSucceedWith $ do
    _ <- defineTestFunc "map" 2 "forall a b. (a -> b) -> ([]) a -> ([]) b"
    _ <- definePartialTestFunc "head" 1 "forall a. ([]) a -> a"
    _ <- defineTestFunc "pairs" 1 "forall a. ([]) a -> ([]) ((,) a)"
    _ <- defineTestFunc "pairs'" 1 "forall a. a -> ([]) a -> ([]) ((,) a)"
    shouldHaveEffect Partiality
      $ Recursive
      [ "pairs xys = case xys of {"
          ++ "    ([])     -> ([]);"
          ++ "    (:) x ys -> pairs' x ys"
          ++ "  }"
      , "pairs' x yxs = case yxs of {"
          ++ "    ([])     -> undefined;"
          ++ "    (:) y xs -> (:) ((,) x y) (pairs xs)"
          ++ "  }"
      ]
  it "adds sharing effect to functions with `let`-expressions"
    $ shouldSucceedWith
    $ do
      _ <- defineTestFunc "comp" 1
        "forall a b c. (b -> c) -> (a -> b) -> a -> c"
      shouldHaveEffect Sharing
        $ NonRecursive
        $ "comp f g x = let { y = g x } in f y"
  it "recognizes functions with tracing effect" $ shouldSucceedWith $ do
    _ <- defineTestFunc "id" 1 "forall a. a -> a"
    shouldHaveEffect Tracing $ NonRecursive $ "id x = trace \"...\" x"
