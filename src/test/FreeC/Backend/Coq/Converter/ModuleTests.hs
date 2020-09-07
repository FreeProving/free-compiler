-- | This module contains tests for "FreeC.Backend.Coq.Converter.Module".
module FreeC.Backend.Coq.Converter.ModuleTests ( testConvertModule ) where

import           Test.Hspec

import           FreeC.Backend.Coq.Converter.Module
import           FreeC.Backend.Coq.Pretty           ()
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Test.Environment
import           FreeC.Test.Expectations
import           FreeC.Test.Parser

-------------------------------------------------------------------------------
-- Expectation Setters                                                       --
-------------------------------------------------------------------------------
-- | Parses the given IR module, converts it to Coq using
--   'convertModule' and sets the expectation that the resulting AST
--   is equal to the given output when pretty printed modulo whitespace.
shouldConvertModuleTo :: [String] -> String -> Converter Expectation
shouldConvertModuleTo inputStrs expectedOutputStr = do
  input <- parseTestModule inputStrs
  output <- convertModule input
  return (output `prettyShouldBe` expectedOutputStr)

-- | Test group for 'convertModule' tests.
testConvertModule :: Spec
testConvertModule = describe "FreeC.Backend.Coq.Converter.Module"
  $ context "Generation of qualified notations"
  $ do
    it "translates empty modules correctly"
      $ shouldSucceedWith
      $ do
        shouldConvertModuleTo ["module A where"]
      $ "(* module A *) From Base Require Import Free. "
    it "produces notations for a single type correctly" $ shouldSucceedWith $ do
      _ <- defineTestTypeCon "A.Foo" 0 ["A.Bar"]
      _ <- defineTestCon "A.Bar" 0 "A.Foo"
      shouldConvertModuleTo ["module A where", "data A.Foo = A.Bar"]
        $ "(* module A *) "
        ++ "From Base Require Import Free. "
        ++ "(* Data type declarations for Foo *) "
        ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type) : Type "
        ++ ":= bar : Foo Shape Pos. "
        ++ "(* Arguments sentences for Foo *) "
        ++ "Arguments bar {Shape} {Pos}. "
        ++ "(* Smart constructors for Foo *) "
        ++ "Notation \"'Bar' Shape Pos\" := "
        ++ "(@pure Shape Pos (Foo Shape Pos) (@bar Shape Pos)) "
        ++ "( at level 10, Shape, Pos at level 9 ). "
        ++ "Notation \"'@Bar' Shape Pos\" := "
        ++ "(@pure Shape Pos (Foo Shape Pos) (@bar Shape Pos)) "
        ++ "( only parsing, at level 10, Shape, Pos at level 9 ). "
        ++ "(* Qualified smart constructors *) "
        ++ "Module QualifiedSmartConstructorModule. "
        ++ "(* Qualified smart constructors for Foo *) "
        ++ "Notation \"'A.Bar' Shape Pos\" := "
        ++ "(@pure Shape Pos (Foo Shape Pos) (@bar Shape Pos)) "
        ++ "( at level 10, Shape, Pos at level 9 ). "
        ++ "Notation \"'@A.Bar' Shape Pos\" := "
        ++ "(@pure Shape Pos (Foo Shape Pos) (@bar Shape Pos)) "
        ++ "( only parsing, at level 10, Shape, Pos at level 9 ). "
        ++ "End QualifiedSmartConstructorModule. "
    it "produces notations for a type with two constructors correctly"
      $ shouldSucceedWith
      $ do
        _ <- defineTestTypeCon "A.Foo" 0 ["A.Bar", "A.Baz"]
        _ <- defineTestCon "A.Bar" 0 "A.Foo"
        _ <- defineTestCon "A.Baz" 0 "A.Foo"
        shouldConvertModuleTo ["module A where", "data A.Foo = A.Bar | A.Baz"]
          $ "(* module A *) "
          ++ "From Base Require Import Free. "
          ++ "(* Data type declarations for Foo *) "
          ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type) : Type "
          ++ ":= bar : Foo Shape Pos | baz : Foo Shape Pos. "
          ++ "(* Arguments sentences for Foo *) "
          ++ "Arguments bar {Shape} {Pos}. "
          ++ "Arguments baz {Shape} {Pos}. "
          ++ "(* Smart constructors for Foo *) "
          ++ "Notation \"'Bar' Shape Pos\" := "
          ++ "(@pure Shape Pos (Foo Shape Pos) (@bar Shape Pos)) "
          ++ "( at level 10, Shape, Pos at level 9 ). "
          ++ "Notation \"'@Bar' Shape Pos\" := "
          ++ "(@pure Shape Pos (Foo Shape Pos) (@bar Shape Pos)) "
          ++ "( only parsing, at level 10, Shape, Pos at level 9 ). "
          ++ "Notation \"'Baz' Shape Pos\" := "
          ++ "(@pure Shape Pos (Foo Shape Pos) (@baz Shape Pos)) "
          ++ "( at level 10, Shape, Pos at level 9 ). "
          ++ "Notation \"'@Baz' Shape Pos\" := "
          ++ "(@pure Shape Pos (Foo Shape Pos) (@baz Shape Pos)) "
          ++ "( only parsing, at level 10, Shape, Pos at level 9 ). "
          ++ "(* Qualified smart constructors *) "
          ++ "Module QualifiedSmartConstructorModule. "
          ++ "(* Qualified smart constructors for Foo *) "
          ++ "Notation \"'A.Bar' Shape Pos\" := "
          ++ "(@pure Shape Pos (Foo Shape Pos) (@bar Shape Pos)) "
          ++ "( at level 10, Shape, Pos at level 9 ). "
          ++ "Notation \"'@A.Bar' Shape Pos\" := "
          ++ "(@pure Shape Pos (Foo Shape Pos) (@bar Shape Pos)) "
          ++ "( only parsing, at level 10, Shape, Pos at level 9 ). "
          ++ "Notation \"'A.Baz' Shape Pos\" := "
          ++ "(@pure Shape Pos (Foo Shape Pos) (@baz Shape Pos)) "
          ++ "( at level 10, Shape, Pos at level 9 ). "
          ++ "Notation \"'@A.Baz' Shape Pos\" := "
          ++ "(@pure Shape Pos (Foo Shape Pos) (@baz Shape Pos)) "
          ++ "( only parsing, at level 10, Shape, Pos at level 9 ). "
          ++ "End QualifiedSmartConstructorModule. "
    it "produces notations for polymorphic types correctly"
      $ shouldSucceedWith
      $ do
        _ <- defineTestTypeCon "A.Foo" 1 ["A.Bar"]
        _ <- defineTestCon "A.Bar" 1 "forall a. a -> A.Foo a"
        shouldConvertModuleTo ["module A where", "data A.Foo a = A.Bar a"]
          $ "(* module A *) "
          ++ "From Base Require Import Free. "
          ++ "(* Data type declarations for Foo *) "
          ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type) "
          ++ "(a : Type) : Type "
          ++ ":= bar : Free Shape Pos a -> Foo Shape Pos a. "
          ++ "(* Arguments sentences for Foo *) "
          ++ "Arguments bar {Shape} {Pos} {a}. "
          ++ "(* Smart constructors for Foo *) "
          ++ "Notation \"'Bar' Shape Pos x_0\" := "
          ++ "(@pure Shape Pos (Foo Shape Pos _) (@bar Shape Pos _ x_0)) "
          ++ "( at level 10, Shape, Pos, x_0 at level 9 ). "
          ++ "Notation \"'@Bar' Shape Pos a x_0\" := "
          ++ "(@pure Shape Pos (Foo Shape Pos a) (@bar Shape Pos a x_0)) "
          ++ "( only parsing, at level 10, Shape, Pos, a, x_0 "
          ++ "at level 9 ). "
          ++ "(* Qualified smart constructors *) "
          ++ "Module QualifiedSmartConstructorModule. "
          ++ "(* Qualified smart constructors for Foo *) "
          ++ "Notation \"'A.Bar' Shape Pos x_0\" := "
          ++ "(@pure Shape Pos (Foo Shape Pos _) (@bar Shape Pos _ x_0)) "
          ++ "( at level 10, Shape, Pos, x_0 at level 9 ). "
          ++ "Notation \"'@A.Bar' Shape Pos a x_0\" := "
          ++ "(@pure Shape Pos (Foo Shape Pos a) (@bar Shape Pos a x_0)) "
          ++ "( only parsing, at level 10, Shape, Pos, a, x_0 "
          ++ "at level 9 ). "
          ++ "End QualifiedSmartConstructorModule. "
    it "produces notations for two data type declarations correctly"
      $ shouldSucceedWith
      $ do
        _ <- defineTestTypeCon "A.Foo1" 0 ["A.Bar1"]
        _ <- defineTestTypeCon "A.Foo2" 0 ["A.Bar2"]
        _ <- defineTestCon "A.Bar1" 0 "A.Foo1"
        _ <- defineTestCon "A.Bar2" 0 "A.Foo2"
        shouldConvertModuleTo
          ["module A where", "data A.Foo1 = A.Bar1;", "data A.Foo2 = A.Bar2"]
          $ "(* module A *) "
          ++ "From Base Require Import Free. "
          ++ "(* Data type declarations for Foo2 *) "
          ++ "Inductive Foo2 (Shape : Type) (Pos : Shape -> Type) : Type "
          ++ ":= bar2 : Foo2 Shape Pos. "
          ++ "(* Arguments sentences for Foo2 *) "
          ++ "Arguments bar2 {Shape} {Pos}. "
          ++ "(* Smart constructors for Foo2 *) "
          ++ "Notation \"'Bar2' Shape Pos\" := "
          ++ "(@pure Shape Pos (Foo2 Shape Pos) (@bar2 Shape Pos)) "
          ++ "( at level 10, Shape, Pos at level 9 ). "
          ++ "Notation \"'@Bar2' Shape Pos\" := "
          ++ "(@pure Shape Pos (Foo2 Shape Pos) (@bar2 Shape Pos)) "
          ++ "( only parsing, at level 10, Shape, Pos at level 9 ). "
          ++ "(* Data type declarations for Foo1 *) "
          ++ "Inductive Foo1 (Shape : Type) (Pos : Shape -> Type) : Type "
          ++ ":= bar1 : Foo1 Shape Pos. "
          ++ "(* Arguments sentences for Foo1 *) "
          ++ "Arguments bar1 {Shape} {Pos}. "
          ++ "(* Smart constructors for Foo1 *) "
          ++ "Notation \"'Bar1' Shape Pos\" := "
          ++ "(@pure Shape Pos (Foo1 Shape Pos) (@bar1 Shape Pos)) "
          ++ "( at level 10, Shape, Pos at level 9 ). "
          ++ "Notation \"'@Bar1' Shape Pos\" := "
          ++ "(@pure Shape Pos (Foo1 Shape Pos) (@bar1 Shape Pos)) "
          ++ "( only parsing, at level 10, Shape, Pos at level 9 ). "
          ++ "(* Qualified smart constructors *) "
          ++ "Module QualifiedSmartConstructorModule. "
          ++ "(* Qualified smart constructors for Foo2 *) "
          ++ "Notation \"'A.Bar2' Shape Pos\" := "
          ++ "(@pure Shape Pos (Foo2 Shape Pos) (@bar2 Shape Pos)) "
          ++ "( at level 10, Shape, Pos at level 9 ). "
          ++ "Notation \"'@A.Bar2' Shape Pos\" := "
          ++ "(@pure Shape Pos (Foo2 Shape Pos) (@bar2 Shape Pos)) "
          ++ "( only parsing, at level 10, Shape, Pos at level 9 ). "
          ++ "(* Qualified smart constructors for Foo1 *) "
          ++ "Notation \"'A.Bar1' Shape Pos\" := "
          ++ "(@pure Shape Pos (Foo1 Shape Pos) (@bar1 Shape Pos)) "
          ++ "( at level 10, Shape, Pos at level 9 ). "
          ++ "Notation \"'@A.Bar1' Shape Pos\" := "
          ++ "(@pure Shape Pos (Foo1 Shape Pos) (@bar1 Shape Pos)) "
          ++ "( only parsing, at level 10, Shape, Pos at level 9 ). "
          ++ "End QualifiedSmartConstructorModule. "
