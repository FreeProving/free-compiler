module Compiler.Converter.ModuleTests where

import           Test.Hspec

import           Compiler.Util.Test

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------

-- | Test group for 'convertModule' tests.
testConvertModule :: Spec
testConvertModule = describe "Compiler.Converter.Module.convertModule" $ do
  testConvertImports

-------------------------------------------------------------------------------
-- Imports                                                                   --
-------------------------------------------------------------------------------

-- | Test group for module imports.
testConvertImports :: Spec
testConvertImports = do
  it "requires an import declaration"
    $  shouldReportFatal
    $  fromModuleConverter
    $  convertTestModule ["module A where", "data A = A"]
    >> convertTestModule ["module B where", "type B = A"]
  it "imports data declarations correctly"
    $ shouldSucceed
    $ fromModuleConverter
    $ do
        _   <- convertTestModule ["module A where", "data A = A"]
        _ <- convertTestModule ["module B where", "import A", "type B = A"]
        return (return ())
  {- FIXME
  it "expands imported type synonyms correctly"
    $ shouldSucceed
    $ fromModuleConverter
    $ do
        _ <- convertTestModule ["module A where", "data A = A"]
        _ <- convertTestModule
          ["module B where", "import A", "type B = A -> Integer"]
        _ <- convertTestModule
          ["module C where", "import B", "foo :: B", "foo x = 0"]
        return (return ())
  -}
