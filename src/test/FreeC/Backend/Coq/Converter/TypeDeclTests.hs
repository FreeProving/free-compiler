-- | This module contains tests for "FreeC.Backend.Coq.Converter.TypeDecl".
module FreeC.Backend.Coq.Converter.TypeDeclTests
  ( testConvertTypeDecl
  , testConvertDataDecls
  ) where

import           Test.Hspec

import           FreeC.Backend.Coq.Converter.TypeDecl
import           FreeC.Backend.Coq.Pretty             ()
import           FreeC.IR.DependencyGraph
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Test.Environment
import           FreeC.Test.Expectations
import           FreeC.Test.Parser

-------------------------------------------------------------------------------
-- Expectation Setters                                                       --
-------------------------------------------------------------------------------
-- | Parses the given type-level IR declarations, converts them to Coq using
--   'convertTypeComponent' and sets the expectation that the resulting AST
--   is equal to the given output when pretty printed modulo whitespace.
shouldConvertLocalTypeDeclsTo
  :: DependencyComponent String -> String -> Converter Expectation
shouldConvertLocalTypeDeclsTo inputStrs expectedOutputStr = do
  input <- parseTestComponent inputStrs
  output <- convertTypeComponent input
  return (output `prettyShouldBe` (expectedOutputStr, ""))

-- | Parses the given type-level IR declarations, converts them to Coq using
--   'convertTypeComponent' and sets the expectation that the second
--   component of the result, which is a list of qualified notations, is equal
--   to the given list when pretty printed modulo whitespace.
shouldProduceQualifiedNotations
  :: DependencyComponent String -> String -> Converter Expectation
shouldProduceQualifiedNotations inputStrs expectedOutputStr = do
  input <- parseTestComponent inputStrs
  (_, outputModule) <- convertTypeComponent input
  return (outputModule `prettyShouldBe` expectedOutputStr)

-------------------------------------------------------------------------------
-- Tests for Type Synonym Declarations                                       --
-------------------------------------------------------------------------------
-- | Test group for 'convertTypeSynDecl' tests.
testConvertTypeDecl :: Spec
testConvertTypeDecl
  = describe "FreeC.Backend.Coq.Converter.TypeDecl.convertTypeSynDecl" $ do
    it "translates non-polymorphic type synonyms correctly"
      $ shouldSucceedWith
      $ do
        "Integer" <- defineTestTypeCon "Integer" 0 []
        "List" <- defineTestTypeCon "List" 1 []
        "TermPos" <- defineTestTypeSyn "TermPos" [] "List Integer"
        shouldConvertLocalTypeDeclsTo
          (NonRecursive "type TermPos = List Integer")
          $ "Definition TermPos (Shape : Type) (Pos : Shape -> Type)"
          ++ "  : Type"
          ++ " := List Shape Pos (Integer Shape Pos)."
    it "translates polymorphic type synonyms correctly" $ shouldSucceedWith $ do
      "List" <- defineTestTypeCon "List" 1 []
      "Pair" <- defineTestTypeCon "Pair" 2 []
      "Queue" <- defineTestTypeSyn "Queue" ["a"] "Pair (List a) (List a)"
      shouldConvertLocalTypeDeclsTo
        (NonRecursive "type Queue a = Pair (List a) (List a)")
        $ "Definition Queue (Shape : Type) (Pos : Shape -> Type)"
        ++ "  (a : Type) : Type"
        ++ " := Pair Shape Pos (List Shape Pos a) (List Shape Pos a)."
    it "expands type synonyms in mutually recursive data type declarations"
      $ shouldSucceedWith
      $ do
        "List" <- defineTestTypeCon "List" 1 []
        "Forest" <- defineTestTypeSyn "Forest" ["a"] "List (Tree a)"
        "Tree" <- defineTestTypeCon "Tree" 1 []
        ("leaf", "Leaf") <- defineTestCon "Leaf" 1 "forall a. a -> Tree a"
        ("branch", "Branch")
          <- defineTestCon "Branch" 1 "forall a. Forest a -> Tree a"
        shouldConvertLocalTypeDeclsTo
          (Recursive [ "type Forest a = List (Tree a)"
                     , "data Tree a = Leaf a | Branch (Forest a)"
                     ])
          $ "(* Data type declarations for Tree *) "
          ++ "Inductive Tree (Shape : Type) (Pos : Shape -> Type) (a : Type)"
          ++ " : Type"
          ++ " := leaf : Free Shape Pos a -> Tree Shape Pos a"
          ++ " |  branch : Free Shape Pos (List Shape Pos (Tree Shape Pos a))"
          ++ "              -> Tree Shape Pos a. "
          ++ "(* Arguments sentences for Tree *) "
          ++ "Arguments leaf {Shape} {Pos} {a}. "
          ++ "Arguments branch {Shape} {Pos} {a}. "
          ++ "(* Smart constructors for Tree *) "
          ++ "Notation \"'Leaf' Shape Pos x_0\" :="
          ++ " (@pure Shape Pos (Tree Shape Pos _) (@leaf Shape Pos _ x_0))"
          ++ " ( at level 10, Shape, Pos, x_0 at level 9 ). "
          ++ "Notation \"'@Leaf' Shape Pos a x_0\" :="
          ++ " (@pure Shape Pos (Tree Shape Pos a) (@leaf Shape Pos a x_0))"
          ++ " ( only parsing, at level 10, Shape, Pos, a, x_0 at level 9 ). "
          ++ "Notation \"'Branch' Shape Pos x_0\" :="
          ++ " (@pure Shape Pos (Tree Shape Pos _) (@branch Shape Pos _ x_0))"
          ++ " ( at level 10, Shape, Pos, x_0 at level 9 ). "
          ++ "Notation \"'@Branch' Shape Pos a x_0\" :="
          ++ " (@pure Shape Pos (Tree Shape Pos a) (@branch Shape Pos a x_0))"
          ++ " ( only parsing, at level 10, Shape, Pos, a, x_0 at level 9 ). "
          ++ "Definition Forest (Shape : Type) (Pos : Shape -> Type)"
          ++ "  (a : Type)"
          ++ " : Type"
          ++ " := List Shape Pos (Tree Shape Pos a)."
    it "sorts type synonym declarations topologically" $ shouldSucceedWith $ do
      "Bar" <- defineTestTypeSyn "Bar" [] "Baz"
      "Baz" <- defineTestTypeSyn "Baz" [] "Foo"
      "Foo" <- defineTestTypeCon "Foo" 1 ["Foo"]
      ("foo", "Foo0") <- defineTestCon "Foo" 2 "Bar -> Baz -> Foo"
      shouldConvertLocalTypeDeclsTo
        (Recursive
         ["type Bar = Baz", "type Baz = Foo", "data Foo = Foo Bar Baz"])
        $ "(* Data type declarations for Foo *) "
        ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type)"
        ++ " : Type"
        ++ " := foo : Free Shape Pos (Foo Shape Pos)"
        ++ "          -> Free Shape Pos (Foo Shape Pos)"
        ++ "          -> Foo Shape Pos. "
        ++ "(* Arguments sentences for Foo *) "
        ++ "Arguments foo {Shape} {Pos}. "
        ++ "(* Smart constructors for Foo *) "
        ++ "Notation \"'Foo0' Shape Pos x_0 x_1\" :="
        ++ " (@pure Shape Pos (Foo Shape Pos) (@foo Shape Pos x_0 x_1))"
        ++ " ( at level 10, Shape, Pos, x_0, x_1 at level 9 ). "
        ++ "Notation \"'@Foo0' Shape Pos x_0 x_1\" :="
        ++ " (@pure Shape Pos (Foo Shape Pos) (@foo Shape Pos x_0 x_1))"
        ++ " ( only parsing, at level 10, Shape, Pos, x_0, x_1 at level 9 ). "
        ++ "Definition Baz (Shape : Type) (Pos : Shape -> Type)"
        ++ " : Type"
        ++ " := Foo Shape Pos. "
        ++ "Definition Bar (Shape : Type) (Pos : Shape -> Type)"
        ++ " : Type"
        ++ " := Baz Shape Pos."
    it "fails if type synonyms form a cycle" $ do
      input <- expectParseTestComponent
        (Recursive ["type Foo = Bar", "type Bar = Foo"])
      shouldFail $ do
        "Foo" <- defineTestTypeSyn "Foo" [] "Bar"
        "Bar" <- defineTestTypeSyn "Bar" [] "Foo"
        convertTypeComponent input

-------------------------------------------------------------------------------
-- Data Type Declarations                                                    --
-------------------------------------------------------------------------------
-- | Test group for 'convertDataDecls' tests.
testConvertDataDecls :: Spec
testConvertDataDecls
  = describe "FreeC.Backend.Coq.Converter.TypeDecl.convertDataDecls" $ do
    context "Translation of types and type synonyms" $ do
      it "translates non-polymorphic data types correctly"
        $ shouldSucceedWith
        $ do
          "Foo" <- defineTestTypeCon "Foo" 0 ["Bar", "Baz"]
          ("bar", "Bar") <- defineTestCon "Bar" 0 "Foo"
          ("baz", "Baz") <- defineTestCon "Baz" 0 "Foo"
          shouldConvertLocalTypeDeclsTo (NonRecursive "data Foo = Bar | Baz")
            $ "(* Data type declarations for Foo *) "
            ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type) : Type "
            ++ " := bar : Foo Shape Pos "
            ++ " |  baz : Foo Shape Pos. "
            ++ "(* Arguments sentences for Foo *) "
            ++ "Arguments bar {Shape} {Pos}. "
            ++ "Arguments baz {Shape} {Pos}. "
            ++ "(* Smart constructors for Foo *) "
            ++ "Notation \"'Bar' Shape Pos\" :="
            ++ " (@pure Shape Pos (Foo Shape Pos) (@bar Shape Pos))"
            ++ " ( at level 10, Shape, Pos at level 9 ). "
            ++ "Notation \"'@Bar' Shape Pos\" :="
            ++ " (@pure Shape Pos (Foo Shape Pos) (@bar Shape Pos))"
            ++ " ( only parsing, at level 10, Shape, Pos at level 9 ). "
            ++ "Notation \"'Baz' Shape Pos\" :="
            ++ " (@pure Shape Pos (Foo Shape Pos) (@baz Shape Pos))"
            ++ " ( at level 10, Shape, Pos at level 9 ). "
            ++ "Notation \"'@Baz' Shape Pos\" :="
            ++ " (@pure Shape Pos (Foo Shape Pos) (@baz Shape Pos))"
            ++ " ( only parsing, at level 10, Shape, Pos at level 9 ). "
      it "translates polymorphic data types correctly" $ shouldSucceedWith $ do
        "Foo" <- defineTestTypeCon "Foo" 2 ["Bar", "Baz"]
        ("bar", "Bar") <- defineTestCon "Bar" 1 "forall a b. a -> Foo a b"
        ("baz", "Baz") <- defineTestCon "Baz" 1 "forall a b. b -> Foo a b"
        shouldConvertLocalTypeDeclsTo
          (NonRecursive "data Foo a b = Bar a | Baz b")
          $ "(* Data type declarations for Foo *) "
          ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type) "
          ++ " (a b : Type) : Type "
          ++ " := bar : Free Shape Pos a -> Foo Shape Pos a b "
          ++ " |  baz : Free Shape Pos b -> Foo Shape Pos a b. "
          ++ "(* Arguments sentences for Foo *) "
          ++ "Arguments bar {Shape} {Pos} {a} {b}. "
          ++ "Arguments baz {Shape} {Pos} {a} {b}. "
          ++ "(* Smart constructors for Foo *) "
          ++ "Notation \"'Bar' Shape Pos x_0\" :="
          ++ " (@pure Shape Pos (Foo Shape Pos _ _) (@bar Shape Pos _ _ x_0))"
          ++ " ( at level 10, Shape, Pos, x_0 at level 9 ). "
          ++ "Notation \"'@Bar' Shape Pos a b x_0\" :="
          ++ " (@pure Shape Pos (Foo Shape Pos a b) (@bar Shape Pos a b x_0))"
          ++ " ( only parsing, at level 10, Shape, Pos, a, b, x_0 at level 9 ). "
          ++ "Notation \"'Baz' Shape Pos x_0\" :="
          ++ " (@pure Shape Pos (Foo Shape Pos _ _) (@baz Shape Pos _ _ x_0))"
          ++ " ( at level 10, Shape, Pos, x_0 at level 9 ). "
          ++ "Notation \"'@Baz' Shape Pos a b x_0\" :="
          ++ " (@pure Shape Pos (Foo Shape Pos a b) (@baz Shape Pos a b x_0))"
          ++ " ( only parsing, at level 10, Shape, Pos, a, b, x_0 at level 9 ). "
      it "renames constructors with same name as their data type"
        $ shouldSucceedWith
        $ do
          "Foo" <- defineTestTypeCon "Foo" 0 ["Foo"]
          ("foo", "Foo0") <- defineTestCon "Foo" 0 "Foo"
          shouldConvertLocalTypeDeclsTo (NonRecursive "data Foo = Foo")
            $ "(* Data type declarations for Foo *) "
            ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type) : Type "
            ++ " := foo : Foo Shape Pos. "
            ++ "(* Arguments sentences for Foo *) "
            ++ "Arguments foo {Shape} {Pos}. "
            ++ "(* Smart constructors for Foo *) "
            ++ "Notation \"'Foo0' Shape Pos\" :="
            ++ " (@pure Shape Pos (Foo Shape Pos) (@foo Shape Pos))"
            ++ " ( at level 10, Shape, Pos at level 9 ). "
            ++ "Notation \"'@Foo0' Shape Pos\" :="
            ++ " (@pure Shape Pos (Foo Shape Pos) (@foo Shape Pos))"
            ++ " ( only parsing, at level 10, Shape, Pos at level 9 ). "
      it "renames type variables with same name as generated constructors"
        $ shouldSucceedWith
        $ do
          "Foo" <- defineTestTypeCon "Foo" 0 ["A"]
          ("a", "A") <- defineTestCon "A" 1 "forall a. a -> Foo a"
          shouldConvertLocalTypeDeclsTo (NonRecursive "data Foo a = A a")
            $ "(* Data type declarations for Foo *) "
            ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type) "
            ++ " (a0 : Type) : Type "
            ++ " := a : Free Shape Pos a0 -> Foo Shape Pos a0. "
            ++ "(* Arguments sentences for Foo *) "
            ++ "Arguments a {Shape} {Pos} {a0}. "
            ++ "(* Smart constructors for Foo *) "
            ++ "Notation \"'A' Shape Pos x_0\" :="
            ++ " (@pure Shape Pos (Foo Shape Pos _) (@a Shape Pos _ x_0))"
            ++ " ( at level 10, Shape, Pos, x_0 at level 9 ). "
            ++ "Notation \"'@A' Shape Pos a0 x_0\" :="
            ++ " (@pure Shape Pos (Foo Shape Pos a0) (@a Shape Pos a0 x_0))"
            ++ " ( only parsing, at level 10, Shape, Pos, a0, x_0 at level 9 ). "
      it "translates mutually recursive data types correctly"
        $ shouldSucceedWith
        $ do
          "Foo" <- defineTestTypeCon "Foo" 0 ["Foo"]
          ("foo", "Foo0") <- defineTestCon "Foo" 1 "Bar -> Foo"
          "Bar" <- defineTestTypeCon "Bar" 0 ["Bar"]
          ("bar", "Bar0") <- defineTestCon "Bar" 1 "Foo -> Bar"
          shouldConvertLocalTypeDeclsTo
            (Recursive ["data Foo = Foo Bar", "data Bar = Bar Foo"])
            $ "(* Data type declarations for Foo, Bar *) "
            ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type) : Type"
            ++ "  := foo : Free Shape Pos (Bar Shape Pos) -> Foo Shape Pos "
            ++ "with Bar (Shape : Type) (Pos : Shape -> Type) : Type"
            ++ "  := bar : Free Shape Pos (Foo Shape Pos) -> Bar Shape Pos. "
            ++ "(* Arguments sentences for Foo *) "
            ++ "Arguments foo {Shape} {Pos}. "
            ++ "(* Smart constructors for Foo *) "
            ++ "Notation \"'Foo0' Shape Pos x_0\" :="
            ++ " (@pure Shape Pos (Foo Shape Pos) (@foo Shape Pos x_0))"
            ++ " ( at level 10, Shape, Pos, x_0 at level 9 ). "
            ++ "Notation \"'@Foo0' Shape Pos x_0\" :="
            ++ " (@pure Shape Pos (Foo Shape Pos) (@foo Shape Pos x_0))"
            ++ " ( only parsing, at level 10, Shape, Pos, x_0 at level 9 ). "
            ++ "(* Arguments sentences for Bar *) "
            ++ "Arguments bar {Shape} {Pos}. "
            ++ "(* Smart constructors for Bar *) "
            ++ "Notation \"'Bar0' Shape Pos x_0\" :="
            ++ " (@pure Shape Pos (Bar Shape Pos) (@bar Shape Pos x_0))"
            ++ " ( at level 10, Shape, Pos, x_0 at level 9 ). "
            ++ "Notation \"'@Bar0' Shape Pos x_0\" :="
            ++ " (@pure Shape Pos (Bar Shape Pos) (@bar Shape Pos x_0))"
            ++ " ( only parsing, at level 10, Shape, Pos, x_0 at level 9 ). "
    context "Generation of qualified smart constructor notations" $ do
      it "produces qualified notations for a single type correctly"
        $ shouldSucceedWith
        $ do
          _ <- defineTestTypeCon "A.Foo" 0 ["A.Bar"]
          _ <- defineTestCon "A.Bar" 0 "A.Foo"
          shouldProduceQualifiedNotations (NonRecursive "data A.Foo = A.Bar")
            $ "(* Qualified smart constructors for Foo *) "
            ++ "Notation \"'A.Bar' Shape Pos\" := "
            ++ "(@pure Shape Pos (Foo Shape Pos) (@bar Shape Pos)) "
            ++ "( at level 10, Shape, Pos at level 9 ). "
            ++ "Notation \"'@A.Bar' Shape Pos\" := "
            ++ "(@pure Shape Pos (Foo Shape Pos) (@bar Shape Pos)) "
            ++ "( only parsing, at level 10, Shape, Pos at level 9 ). "
      it "produces notations for a type with two constructors correctly"
        $ shouldSucceedWith
        $ do
          _ <- defineTestTypeCon "A.Foo" 0 ["A.Bar", "A.Baz"]
          _ <- defineTestCon "A.Bar" 0 "A.Foo"
          _ <- defineTestCon "A.Baz" 0 "A.Foo"
          shouldProduceQualifiedNotations
            (NonRecursive "data A.Foo = A.Bar | A.Baz")
            $ "(* Qualified smart constructors for Foo *) "
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
      it "produces notations for polymorphic types correctly"
        $ shouldSucceedWith
        $ do
          _ <- defineTestTypeCon "A.Foo" 1 ["A.Bar"]
          _ <- defineTestCon "A.Bar" 1 "forall a. a -> A.Foo a"
          shouldProduceQualifiedNotations
            (NonRecursive "data A.Foo a = A.Bar a")
            $ "(* Qualified smart constructors for Foo *) "
            ++ "Notation \"'A.Bar' Shape Pos x_0\" := "
            ++ "(@pure Shape Pos (Foo Shape Pos _) (@bar Shape Pos _ x_0)) "
            ++ "( at level 10, Shape, Pos, x_0 at level 9 ). "
            ++ "Notation \"'@A.Bar' Shape Pos a x_0\" := "
            ++ "(@pure Shape Pos (Foo Shape Pos a) (@bar Shape Pos a x_0)) "
            ++ "( only parsing, at level 10, Shape, Pos, a, x_0 "
            ++ "at level 9 ). "
      it "produces notations for two mutually recursive types correctly"
        $ shouldSucceedWith
        $ do
          _ <- defineTestTypeCon "A.Foo1" 1 ["A.Bar1"]
          _ <- defineTestTypeCon "A.Foo2" 1 ["A.Bar2"]
          _ <- defineTestCon "A.Bar1" 1 "A.Foo2 -> A.Foo1"
          _ <- defineTestCon "A.Bar2" 1 "A.Foo1 -> A.Foo2"
          shouldProduceQualifiedNotations
            (Recursive
             ["data A.Foo1 a = A.Bar1 A.Foo2", "data A.Foo2 a = A.Bar2 A.Foo1"])
            $ "(* Qualified smart constructors for Foo1 *) "
            ++ "Notation \"'A.Bar1' Shape Pos x_0\" := "
            ++ "(@pure Shape Pos _ (@bar1 Shape Pos _ x_0)) "
            ++ "( at level 10, Shape, Pos, x_0 at level 9 ). "
            ++ "Notation \"'@A.Bar1' Shape Pos a x_0\" := "
            ++ "(@pure Shape Pos (Foo1 Shape Pos) (@bar1 Shape Pos a x_0)) "
            ++ "( only parsing, at level 10, Shape, Pos, a, x_0 at level 9 ). "
            ++ "(* Qualified smart constructors for Foo2 *) "
            ++ "Notation \"'A.Bar2' Shape Pos x_0\" := "
            ++ "(@pure Shape Pos _ (@bar2 Shape Pos _ x_0)) "
            ++ "( at level 10, Shape, Pos, x_0 at level 9 ). "
            ++ "Notation \"'@A.Bar2' Shape Pos a x_0\" := "
            ++ "(@pure Shape Pos (Foo2 Shape Pos) (@bar2 Shape Pos a x_0)) "
            ++ "( only parsing, at level 10, Shape, Pos, a, x_0 at level 9 )."


