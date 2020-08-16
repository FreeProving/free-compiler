-- | This module contains tests for "FreeC.Backend.Agda.Converter.TypeDecl".
module FreeC.Backend.Agda.Converter.TypeDeclTests ( testConvertDataDecls ) where

import           Test.Hspec

import           FreeC.Backend.Agda.Converter.TypeDecl ( convertTypeDecls )
import           FreeC.Backend.Agda.Pretty             ()
import           FreeC.IR.DependencyGraph
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Pretty                          ( showPretty )
import           FreeC.Test.Environment
import           FreeC.Test.Expectations
import           FreeC.Test.Parser

-- | Parses the given type-level IR declarations, converts them to Agda using
--   'convertTypeDecls' and sets the expectation that the resulting AST
--   is equal to the given output when pretty printed modulo white
--   space.
shouldConvertTypeDeclsTo
  :: DependencyComponent String -> [ String ] -> Converter Expectation
shouldConvertTypeDeclsTo inputStrs expectedOutput = do
  input <- parseTestComponent inputStrs
  output <- convertTypeDecls input
  return (output `prettyShouldBe` showPretty expectedOutput)

-- | Test group for @convertTypeDecls@ tests.
testConvertDataDecls :: Spec
testConvertDataDecls
  = describe "FreeC.Backend.Agda.Converter.TypeDecl.convertTypeDecl" $ do
    it "translates non-polymorphic, non-recursive data types correctly"
      $ shouldSucceedWith $ do
        "Foo" <- defineTestTypeCon "Foo" 0 [ "Bar", "Baz" ]
        ("bar", "Bar") <- defineTestCon "Bar" 0 "Foo"
        ("baz", "Baz") <- defineTestCon "Baz" 0 "Foo"
        shouldConvertTypeDeclsTo (NonRecursive "data Foo = Bar | Baz")
          [ "data Foo (Shape : Set)(Pos : Shape → Set) : Set where"
              ++ "  bar : Foo Shape Pos" ++ "  baz : Foo Shape Pos"
          , "pattern Bar = pure bar"
          , "pattern Baz = pure baz"
          ]
    it "annotates recursive data type with Sized type" $ shouldSucceedWith $ do
      "List" <- defineTestTypeCon "List" 1 [ "Nil", "Cons" ]
      ("nil", "Nil") <- defineTestCon "Nil" 0 "List"
      ("cons", "Cons") <- defineTestCon "Cons" 2 "List"
      shouldConvertTypeDeclsTo
        (Recursive [ "data List a = Nil | Cons a (List a)" ])
        [ "data List (Shape : Set)(Pos : Shape → Set)(a : Set) : {Size} → Set where"
            ++ "  nil : List Shape Pos a"
            ++ "  cons : ∀ {i} → Free Shape Pos a → Free Shape Pos (List Shape Pos a {i}) → List Shape Pos a {↑ i}"
        , "pattern Nil = pure nil"
        , "pattern Cons x x₁ = pure (cons x x₁)"
        ]

