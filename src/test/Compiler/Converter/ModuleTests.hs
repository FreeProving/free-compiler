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
  testQualifiedNames

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
        _ <- convertTestModule ["module A where", "data A = A"]
        _ <- convertTestModule ["module B where", "import A", "type B = A"]
        return (return ())
  it "allows ambigious imports of names that are not referenced"
    $ shouldSucceed
    $ fromModuleConverter
    $ do
        _ <- convertTestModule ["module A where", "foo :: ()", "foo = ()"]
        _ <- convertTestModule ["module B where", "foo :: ()", "foo = ()"]
        _ <- convertTestModule ["module C where", "import A", "import B"]
        return (return ())
  it "does not allow ambigious imports of names that are referenced"
    $ shouldReportFatal
    $ fromModuleConverter
    $ do
        _ <- convertTestModule ["module A where", "foo :: ()", "foo = ()"]
        _ <- convertTestModule ["module B where", "foo :: ()", "foo = ()"]
        convertTestModule
          ["module C where", "import A", "import B", "bar :: ()", "bar = foo"]
  it "does not export imported entries"
    $ shouldReportFatal
    $ fromModuleConverter
    $ do
        _ <- convertTestModule ["module A where", "type A = ()"]
        _ <- convertTestModule ["module B where", "import A"]
        convertTestModule ["module C where", "import B", "type B = A"]
  it "expands imported type synonyms correctly"
    $ shouldSucceed
    $ fromModuleConverter
    $ do
        _ <- convertTestModule ["module A where", "data A = A"]
        _ <- convertTestModule
          ["module B where", "import A", "type B = A -> ()"]
        _ <- convertTestModule
          ["module C where", "import B", "foo :: B", "foo x = ()"]
        return (return ())
  it "local entries don't conflict with hidden entries"
    $ shouldSucceed
    $ fromModuleConverter
    $ do
        _ <- convertTestModule ["module A where", "data A = A"]
        _ <- convertTestModule
          ["module B where", "import A", "type B = A -> ()"]
        shouldTranslateModuleTo
          [ "module C where"
          , "import B"
          , "type A = ()"
          , "foo :: B"
          , "foo x = ()"
          ]
          [ "(* module C *)"
          , "From Base Require Import Free."
          , "From Base Require Import Prelude."
          , "From Generated Require Export B."
          , "Definition A1 (Shape : Type) (Pos : Shape -> Type) : Type"
          , "  := Unit Shape Pos."
          , "Definition foo (Shape : Type) (Pos : Shape -> Type)"
          , "               (x : Free Shape Pos (A Shape Pos))"
          , "   : Free Shape Pos (Unit Shape Pos)"
          , "  := Tt Shape Pos."
          ]

-------------------------------------------------------------------------------
-- Qualified Identifiers                                                     --
-------------------------------------------------------------------------------

-- | Test group for qualified identifiers.
testQualifiedNames :: Spec
testQualifiedNames = do
  it "top-level declarations are in scope unqualified"
    $ shouldSucceed
    $ fromModuleConverter
    $ do
        _ <- convertTestModule
          ["module M where", "f :: a -> a", "f x = x", "g :: ()", "g = f ()"]
        return (return ())
  it "top-level declarations are in scope qualified"
    $ shouldSucceed
    $ fromModuleConverter
    $ do
        _ <- convertTestModule
          [ "module M where"
          , "f :: a -> a"
          , "f x = x"
          , "g :: (a -> b) -> a -> b"
          , "g f x = M.f f x"
          ]
        return (return ())
  it "imported entries are in scope qualified"
    $ shouldSucceed
    $ fromModuleConverter
    $ do
        _ <- convertTestModule ["module A where", "data A = A"]
        _ <- convertTestModule
          ["module B where", "import A", "foo :: A", "foo = A.A"]
        return (return ())
  it "hidden entries of imported modules are not in scope"
    $ shouldReportFatal
    $ fromModuleConverter
    $ do
        _ <- convertTestModule ["module A where", "data A = A"]
        _ <- convertTestModule ["module B where", "import A", "type B = A"]
        convertTestModule
          ["module C where", "import B", "foo :: B", "foo = A.A"]
