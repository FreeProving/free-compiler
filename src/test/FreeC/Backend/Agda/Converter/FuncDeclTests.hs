-- | This module contains tests for "FreeC.Backend.Agda.Converter.FuncDecl".

module FreeC.Backend.Agda.Converter.FuncDeclTests
  ( testConvertFuncDecls
  )
where

import           Test.Hspec

import           FreeC.Backend.Agda.Converter.FuncDecl
                                                ( convertFuncDecls )
import           FreeC.Backend.Agda.Pretty      ( )
import           FreeC.IR.DependencyGraph
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Test.Parser
import           FreeC.Test.Environment
import           FreeC.Test.Expectations
import           FreeC.Pretty                   ( showPretty )

-- | Parses the given IR function declaration, converts it to Agda using
--   'convertFuncDecls' and sets the expectation that the resulting
--   Agda code equals the given expected output modulo white space.
shouldConvertTypeDeclsTo
  :: DependencyComponent String -> [String] -> Converter Expectation
shouldConvertTypeDeclsTo inputStrs expectedOutput = do
  input  <- parseTestComponent inputStrs
  output <- convertFuncDecls input
  return (output `prettyShouldBe` showPretty expectedOutput)

-- | Test group for @convertFuncDecls@ tests.
testConvertFuncDecls :: Spec
testConvertFuncDecls =
  describe "FreeC.Backend.Agda.Converter.TypeDecl.convertFuncDecl" $ do
    it "translates 0-ary functions correctly" $ shouldSucceedWith $ do
      "Integer" <- defineTestTypeCon "Integer" 0 []
      "foo"     <- defineTestFunc "foo" 0 "Integer"
      shouldConvertTypeDeclsTo
        (NonRecursive "foo :: Integer = 42")
        ["foo : \x2200 {Shape} {Pos} \x2192 Free Shape Pos (Integer Shape Pos)"]

    it "translates polymorphic functions correctly" $ shouldSucceedWith $ do
      "foo" <- defineTestFunc "foo" 0 "forall a. a -> a"
      shouldConvertTypeDeclsTo
        (NonRecursive "foo @a (x :: a) :: a = x")
        [ "foo : \x2200 {Shape} {Pos} {a} \x2192 Free Shape Pos a "
            ++ "\x2192 Free Shape Pos a"
        ]

    it "uses type information from the AST not the environment"
      $ shouldSucceedWith
      $ do
          "foo" <- defineTestFunc "foo" 0 "forall b. b -> b"
          shouldConvertTypeDeclsTo
            (NonRecursive "foo @a (x :: a) :: a = x")
            [ "foo : \x2200 {Shape} {Pos} {a} \x2192 Free Shape Pos a "
                ++ "\x2192 Free Shape Pos a"
            ]

    it "translates functions with multiple arguments correctly"
      $ shouldSucceedWith
      $ do
          "Pair"       <- defineTestTypeCon "Pair" 0 ["Pair"]
          (_, "Pair0") <- defineTestCon "Pair"
                                        2
                                        "forall a b. a -> b -> Pair a b"
          "foo" <- defineTestFunc "foo" 0 "forall a b. a -> b -> Pair a b"
          shouldConvertTypeDeclsTo
            (NonRecursive
              "foo @a @b (x :: a) (y :: b) :: Pair a b = Pair @a @b x y"
            )
            [ "foo : \x2200 {Shape} {Pos} {a} {b} \x2192 Free Shape Pos a "
              ++ "\x2192 Free Shape Pos b "
              ++ "\x2192 Free Shape Pos (Pair Shape Pos a b)"
            ]

    it "translates higher order functions correctly" $ shouldSucceedWith $ do
      "Pair" <- defineTestTypeCon "Pair" 0 ["Pair"]
      (_, "Pair0") <- defineTestCon "Pair" 2 "forall a b. a -> b -> Pair a b"
      "curry" <- defineTestFunc "curry"
                                0
                                "forall a b c. (Pair a b -> c) -> a -> b -> c"
      shouldConvertTypeDeclsTo
        (  NonRecursive
        $  "curry @a @b @c (f :: Pair a b -> c) (x :: a) (y :: b) :: c "
        ++ "= f (Pair @a @b x y)"
        )
        [ "curry : \x2200 {Shape} {Pos} {a} {b} {c} "
          ++ "\x2192 Free Shape Pos (Free Shape Pos (Pair Shape Pos a b) "
          ++ "\x2192 Free Shape Pos c) \x2192 Free Shape Pos a "
          ++ "\x2192 Free Shape Pos b \x2192 Free Shape Pos c"
        ]
