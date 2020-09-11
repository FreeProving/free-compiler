-- | Test group for tests of modules below @FreeC.Frontend.Haskell@.
module FreeC.Frontend.Haskell.Tests ( testHaskellFrontend ) where

import           Test.Hspec

import           FreeC.Frontend.Haskell.SimplifierTests

-- | Test group for tests of modules below @FreeC.Frontend.Haskell@.
testHaskellFrontend :: Spec
testHaskellFrontend = do
  testSimplifier
