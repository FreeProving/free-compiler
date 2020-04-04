-- | This module contains tests for "FreeC.Pass.PartialityAnalysisPass".

module FreeC.Pass.PartialityAnalysisPassTests
  ( testPartialityAnalysisPass
  )
where

import           Test.Hspec

import           FreeC.Environment
import           FreeC.IR.DependencyGraph
import qualified FreeC.IR.Syntax               as HS
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Pass.PartialityAnalysisPass
import           FreeC.Test.Environment
import           FreeC.Test.Parser
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Expectation setters                                                       --
-------------------------------------------------------------------------------

-- | Parses the given function declarations, runs the 'defineFuncDeclsPass' and
--   'partialityAnalysisPass' after each other and sets the expectation that
--   there is an environment entry for each function that marks it as partial.
--
--   The first argument determines whether the function declarations are
--   mutually 'recursive' or there is only a single 'nonRecursive' function.
shouldBePartial
  :: ([HS.FuncDecl] -> DependencyComponent HS.FuncDecl)
  -> [String]
  -> Converter Expectation
shouldBePartial = shouldBePartialWith $ \funcName partial -> if partial
  then return ()
  else
    expectationFailure
    $  "Expected "
    ++ showPretty funcName
    ++ " to be partial, but it has not been marked as partial."

-- | Like 'shouldBePartial' but sets the expectation that none of the
--   functions are partial.
shouldNotBePartial
  :: ([HS.FuncDecl] -> DependencyComponent HS.FuncDecl)
  -> [String]
  -> Converter Expectation
shouldNotBePartial = shouldBePartialWith $ \funcName partial -> if not partial
  then return ()
  else
    expectationFailure
    $  "Expected "
    ++ showPretty funcName
    ++ " to be non-partial, but it has been marked as partial."

-- | Common implementation of 'shouldBePartial' and 'shouldNotBePartial'.
shouldBePartialWith
  :: (HS.QName -> Bool -> Expectation)
  -> ([HS.FuncDecl] -> DependencyComponent HS.FuncDecl)
  -> [String]
  -> Converter Expectation
shouldBePartialWith setExpectation mkComponent inputs = do
  funcDecls <- mapM parseTestFuncDecl inputs
  let funcNames = map HS.funcDeclQName funcDecls
      component = mkComponent funcDecls
  _        <- partialityAnalysisPass component
  partials <- mapM (inEnv . isPartial) funcNames
  let expectations = zipWith setExpectation funcNames partials
  return (sequence_ expectations)

-- | Smart constructor for 'NonRecursive' that takes an one elementary list.
nonRecursive :: [HS.FuncDecl] -> DependencyComponent HS.FuncDecl
nonRecursive = NonRecursive . head

-- | Alias for 'Recursive' for consistency with 'nonRecursive'.
recursive :: [HS.FuncDecl] -> DependencyComponent HS.FuncDecl
recursive = Recursive

-------------------------------------------------------------------------------
-- Tests                                                                     --
-------------------------------------------------------------------------------

-- | Test group for 'partialityAnalysisPass' tests.
testPartialityAnalysisPass :: Spec
testPartialityAnalysisPass = describe "FreeC.Pass.PartialityAnalysisPass" $ do
  it "does not classify non-partial functions as partial"
    $ shouldSucceedWith
    $ do
        _ <- defineTestFunc "maybeHead" 1 "([]) a -> Maybe a"
        shouldNotBePartial
          nonRecursive
          [ "maybeHead xs = case xs of {"
            ++ "  ([])      -> Nothing;"
            ++ "  (:) x xs' -> Just x"
            ++ "}"
          ]

  it "recognizes directly partial functions using 'undefined'"
    $ shouldSucceedWith
    $ do
        _ <- defineTestFunc "head" 1 "([]) a -> a"
        shouldBePartial
          nonRecursive
          [ "head xs = case xs of {"
            ++ "  ([])      -> undefined;"
            ++ "  (:) x xs' -> x"
            ++ "}"
          ]

  it "recognizes directly partial functions using 'error'"
    $ shouldSucceedWith
    $ do
        _ <- defineTestFunc "head" 1 "([]) a -> a"
        shouldBePartial
          nonRecursive
          [ "head xs = case xs of {"
            ++ "  ([])      -> error \"head: empty list\";"
            ++ "  (:) x xs' -> x"
            ++ "}"
          ]

  it "recognizes indirectly partial functions" $ shouldSucceedWith $ do
    _ <- defineTestFunc "map" 2 "(a -> b) -> ([]) a -> ([]) b"
    _ <- definePartialTestFunc "head" 1 "([]) a -> a"
    _ <- definePartialTestFunc "heads" 1 "([]) a -> ([]) a"
    shouldBePartial nonRecursive ["heads = map head"]

  it "recognizes mutually recursive partial functions" $ shouldSucceedWith $ do
    _ <- defineTestFunc "map" 2 "(a -> b) -> ([]) a -> ([]) b"
    _ <- definePartialTestFunc "head" 1 "([]) a -> a"
    _ <- definePartialTestFunc "pairs" 1 "([]) a -> ([]) ((,) a)"
    _ <- definePartialTestFunc "pairs'" 1 "a -> ([]) a -> ([]) ((,) a)"
    shouldBePartial
      recursive
      [ "pairs xys = case xys of {"
      ++ "    ([])     -> ([]);"
      ++ "    (:) x ys -> pairs' x ys"
      ++ "  }"
      , "pairs' x yxs = case yxs of {"
      ++ "    ([])     -> undefined;"
      ++ "    (:) y xs -> (:) ((,) x y) (pairs xs)"
      ++ "  }"
      ]
