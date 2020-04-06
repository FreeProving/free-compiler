-- | This module contains tests for passes that are part of the compiler
--   pipeline "FreeC.Pipeline".

module FreeC.PipelineTests
  ( testPipeline
  )
where

import           Test.Hspec

import           FreeC.Pass.EtaConversionPassTests
import           FreeC.Pass.PartialityAnalysisPassTests

-- | Test group for 'FreeC.Pipeline.runPipeline' tests.
testPipeline :: Spec
testPipeline = do
  testPartialityAnalysisPass
  testEtaConversionPass
