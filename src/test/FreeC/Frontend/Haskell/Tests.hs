-- | This module contains tests for modules with the @FreeC.Frontend.Haskell@
--   prefix.
module FreeC.Frontend.Haskell.Tests ( testHaskellFrontend ) where

import           Test.Hspec

import           FreeC.Frontend.Haskell.SimplifierTests

-- | Test group for tests of modules with the @FreeC.Frontend.Haskell@ prefix.
testHaskellFrontend :: Spec
testHaskellFrontend = do
  testSimplifier
