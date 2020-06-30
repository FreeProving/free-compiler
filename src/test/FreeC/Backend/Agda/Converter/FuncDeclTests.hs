-- | This module contains tests for "FreeC.Backend.Agda.Converter.FuncDecl".
--
--   Agda source code uses 

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
--   Agda code equals the given expected output modulo whitespace.
shouldConvertFuncDeclsTo
  :: DependencyComponent String -> [String] -> Converter Expectation
shouldConvertFuncDeclsTo inputStrs expectedOutput = do
  input  <- parseTestComponent inputStrs
  output <- convertFuncDecls input
  return (output `prettyShouldBe` showPretty expectedOutput)

-- | Test group for 'convertFuncDecls' tests.
testConvertFuncDecls :: Spec
testConvertFuncDecls =
  describe "FreeC.Backend.Agda.Converter.FuncDecl.convertFuncDecl" $ do
    it "translates 0-ary functions correctly" $ shouldSucceedWith $ do
      "Integer" <- defineTestTypeCon "Integer" 0 []
      "foo"     <- defineTestFunc "foo" 0 "Integer"
      shouldConvertFuncDeclsTo
        (NonRecursive "foo :: Integer = 42")
        [ "foo : ∀ {Shape} {Pos} → Free Shape Pos (Integer Shape Pos)"
        , "foo = 42"
        ]

    it "translates polymorphic functions correctly" $ shouldSucceedWith $ do
      "foo" <- defineTestFunc "foo" 0 "forall a. a -> a"
      shouldConvertFuncDeclsTo
        (NonRecursive "foo @a (x :: a) :: a = x")
        [ "foo : ∀ {Shape} {Pos} {a} → Free Shape Pos a "
          ++ "→ Free Shape Pos a"
        , "foo x = x"
        ]

    it "uses type information from the AST not the environment"
      $ shouldSucceedWith
      $ do
          "foo" <- defineTestFunc "foo" 0 "forall b. b -> b"
          shouldConvertFuncDeclsTo
            (NonRecursive "foo @a (x :: a) :: a = x")
            [ "foo : ∀ {Shape} {Pos} {a} → Free Shape Pos a "
                ++ "→ Free Shape Pos a"
            , "foo x = x"
            ]

    it "translates functions with multiple arguments correctly"
      $ shouldSucceedWith
      $ do
          "Pair"       <- defineTestTypeCon "Pair" 0 ["Pair"]
          (_, "Pair0") <- defineTestCon "Pair"
                                        2
                                        "forall a b. a -> b -> Pair a b"
          "foo" <- defineTestFunc "foo" 0 "forall a b. a -> b -> Pair a b"
          shouldConvertFuncDeclsTo
            (NonRecursive
              "foo @a @b (x :: a) (y :: b) :: Pair a b = Pair @a @b x y"
            )
            [ "foo : ∀ {Shape} {Pos} {a} {b} → Free Shape Pos a "
              ++ "→ Free Shape Pos b "
              ++ "→ Free Shape Pos (Pair Shape Pos a b)"
            , "foo x y = Pair x y"
            ]

    it "translates higher order functions correctly" $ shouldSucceedWith $ do
      "Pair" <- defineTestTypeCon "Pair" 0 ["Pair"]
      (_, "Pair0") <- defineTestCon "Pair" 2 "forall a b. a -> b -> Pair a b"
      "curry" <- defineTestFunc "curry"
                                0
                                "forall a b c. (Pair a b -> c) -> a -> b -> c"
      shouldConvertFuncDeclsTo
        (  NonRecursive
        $  "curry @a @b @c (f :: Pair a b -> c) (x :: a) (y :: b) :: c "
        ++ "= f (Pair @a @b x y)"
        )
        [ "curry : ∀ {Shape} {Pos} {a} {b} {c} "
          ++ "→ Free Shape Pos"
          ++ "  (Free Shape Pos (Pair Shape Pos a b) → Free Shape Pos c) "
          ++ "→ Free Shape Pos a "
          ++ "→ Free Shape Pos b → Free Shape Pos c"
        , "curry f x y = f >>= λ where"
        , "  f₀ → f₀ (Pair x y)"
        ]
