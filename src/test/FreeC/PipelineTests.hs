-- | This module contains tests for passes that are part of the compiler
--   pipeline "FreeC.Pipeline".

module FreeC.PipelineTests
  ( testPipeline
  )
where

import           Test.Hspec

import           FreeC.Pass.CompletePatternPassTests
import           FreeC.Pass.EtaConversionPassTests
import           FreeC.Pass.PartialityAnalysisPassTests
import           FreeC.Pass.ResolverPassTests
import           FreeC.Pass.TypeInferencePassTests

-- | Test group for 'FreeC.Pipeline.runPipeline' tests.
testPipeline :: Spec
testPipeline = do
  testEtaConversionPass
  testPartialityAnalysisPass
  testResolverPass
  testTypeInferencePass
  testCompletePatternPass
