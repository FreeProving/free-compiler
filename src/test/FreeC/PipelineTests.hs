-- | This module contains tests for passes that are part of the compiler
--   pipeline (see "FreeC.Pipeline").
module FreeC.PipelineTests ( testPipeline ) where

import           Test.Hspec

import           FreeC.Pass.CompletePatternPassTests
import           FreeC.Pass.EffectAnalysisPassTests
import           FreeC.Pass.EtaConversionPassTests
import           FreeC.Pass.ExportPassTests
import           FreeC.Pass.FlattenExprPassTests
import           FreeC.Pass.InlineLambdaPassTests
import           FreeC.Pass.KindCheckPassTests
import           FreeC.Pass.LetSortPassTests
import           FreeC.Pass.ResolverPassTests
import           FreeC.Pass.TypeInferencePassTests

-- | Test group for tests of passes in 'FreeC.Pipeline.pipeline'.
testPipeline :: Spec
testPipeline = do
  testCompletePatternPass
  testEffectAnalysisPass
  testEtaConversionPass
  testExportPass
  testFlattenExprPass
  testInlineLambdaPass
  testKindCheckPass
  testLetSortPass
  testResolverPass
  testTypeInferencePass
