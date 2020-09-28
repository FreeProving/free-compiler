-- | This module contains tests for "FreeC.Pass.ResolverPass".
module FreeC.Pass.ResolverPassTests ( testResolverPass ) where

import           Test.Hspec

import           FreeC.Monad.Class.Testable
import           FreeC.Pass.ResolverPass
import           FreeC.Test.Parser

-- | Test group for "FreeC.Pass.ResolverPass" tests.
testResolverPass :: Spec
testResolverPass = describe "FreeC.Pass.ResolverPass" $ do
  testRedefinition

-- | Test group for tests that check that the resolver pass rejects modules
--   with multiple declarations of the same identifier at the same level
--   but allows the same identifier on different levels or in different
--   name spaces.
testRedefinition :: Spec
testRedefinition = context "redefinition" $ do
  context "data types" $ do
    it "accepts data type and constructor with same name" $ do
      input <- expectParseTestModule ["module M where", "data Foo = Foo;"]
      shouldSucceed (resolverPass input)
    it "rejects data type declarations with same name" $ do
      input <- expectParseTestModule
        ["module M where", "data Foo = Foo;", "data Foo = Bar;"]
      shouldFail (resolverPass input)
    it "rejects constructors with same name in same data type" $ do
      input
        <- expectParseTestModule ["module M where", "data Foo = Foo | Foo;"]
      shouldFail (resolverPass input)
    it "rejects constructors with same name in different data types" $ do
      input <- expectParseTestModule
        ["module M where", "data Foo = Foo;", "data Bar = Foo;"]
      shouldFail (resolverPass input)
    it "rejects type arguments of data type with same name" $ do
      input
        <- expectParseTestModule ["module M where", "data Foo a a = Foo a;"]
      shouldFail (resolverPass input)
  context "type synonyms" $ do
    it "rejects type synonym declarations with same name" $ do
      input <- expectParseTestModule
        [ "module M where"
        , "import Prelude;"
        , "type Foo = Integer;"
        , "type Foo a = Prelude.([]) a;"
        ]
      shouldFail (resolverPass input)
    it "rejects type arguments of type synonym with same name" $ do
      input <- expectParseTestModule
        ["module M where", "import Prelude;", "type Foo a a = Prelude.([]) a;"]
      shouldFail (resolverPass input)
  context "function declarations" $ do
    it "rejects function declarations with same name" $ do
      input
        <- expectParseTestModule ["module M where", "foo = 42;", "foo = 1337"]
      shouldFail (resolverPass input)
    it "rejects function arguments with same name" $ do
      input <- expectParseTestModule ["module M where", "const x x = x;"]
      shouldFail (resolverPass input)
    it "rejects function type arguments with same name" $ do
      input <- expectParseTestModule ["module M where", "id @a @a x = x;"]
      shouldFail (resolverPass input)
  context "variable patterns" $ do
    it "accepts lambda abstraction arguments to shadow other variables" $ do
      input <- expectParseTestModule ["module M where", "foo x = \\x -> x"]
      shouldSucceed (resolverPass input)
    it "rejects variable patterns with same name in lambda abstraction" $ do
      input <- expectParseTestModule ["module M where", "foo = \\x x -> x"]
      shouldFail (resolverPass input)
    it "rejects variable patterns with same name in case expression" $ do
      input <- expectParseTestModule
        [ "module M where"
        , "import Prelude;"
        , "head xs = case xs of {"
            ++ "    Prelude.([]) -> undefined;"
            ++ "    Prelude.(:) x x -> x"
            ++ "  }"
        ]
      shouldFail (resolverPass input)
    it "accepts variable patterns to shadow other variables" $ do
      input <- expectParseTestModule
        [ "module M where"
        , "import Prelude;"
        , "head xs = case xs of {"
            ++ "    Prelude.([]) -> undefined;"
            ++ "    Prelude.(:) x xs -> x"
            ++ "  }"
        ]
      shouldSucceed (resolverPass input)
