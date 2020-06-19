-- | This module contains tests for "FreeC.Backend.Agda.Converter.TypeDecl".

module FreeC.Backend.Agda.Converter.TypeDeclTests
  ( testConvertDataDecls
  )
where

import           Test.Hspec

import           FreeC.Backend.Agda.Converter.TypeDecl
                                                ( convertTypeDecls )
import           FreeC.Backend.Agda.Pretty      ( )
import           FreeC.IR.DependencyGraph
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Test.Parser
import           FreeC.Test.Environment
import           FreeC.Test.Expectations
import           FreeC.Pretty                   ( Pretty
                                                , showPretty
                                                )

shouldConvertTypeDeclsTo
  :: (Pretty a) => DependencyComponent String -> a -> Converter Expectation
shouldConvertTypeDeclsTo inputStrs expectedOutput = do
  input  <- parseTestComponent inputStrs
  output <- convertTypeDecls input
  return (output `prettyShouldBe` showPretty expectedOutput)

testConvertDataDecls :: Spec
testConvertDataDecls =
  describe "FreeC.Backend.Agda.Converter.TypeDecl.convertTypeDecl" $ do
    it "translates non-polymorphic, non-recursive data types correctly"
      $ shouldSucceedWith
      $ do
          "Foo"          <- defineTestTypeCon "Foo" 0
          ("bar", "Bar") <- defineTestCon "Bar" 0 "Foo"
          ("baz", "Baz") <- defineTestCon "Baz" 0 "Foo"
          shouldConvertTypeDeclsTo
            (NonRecursive "data Foo = Bar | Baz")
            [ "data Foo (Shape : Set)(Pos : Shape \8594 Set) : Set where"
            ++ "  bar : Foo Shape Pos"
            ++ "  baz : Foo Shape Pos"
            , "pattern Bar = pure bar"
            , "pattern Baz = pure baz"
            ]
    it "annotates recursive data type with Sized type" $ shouldSucceedWith $ do
      "List"           <- defineTestTypeCon "List" 1
      ("nil" , "Nil" ) <- defineTestCon "Nil" 0 "List"
      ("cons", "Cons") <- defineTestCon "Cons" 2 "List"
      shouldConvertTypeDeclsTo
        (Recursive ["data List a = Nil | Cons a (List a)"])
        [ "data List (Shape : Set)(Pos : Shape \8594 Set)(a : Set) : {Size} \8594 Set where"
        ++ "  nil : \x2200 {i} \8594 List Shape Pos a {\x2191 i}"
        ++ "  cons : \x2200 {i} \8594 Free Shape Pos a \8594 Free Shape Pos (List Shape Pos a {i}) \8594 List Shape Pos a {\x2191 i}"
        , "pattern Nil = pure nil"
        , "pattern Cons x x\x2081 = pure (cons x x\x2081)"
        ]

