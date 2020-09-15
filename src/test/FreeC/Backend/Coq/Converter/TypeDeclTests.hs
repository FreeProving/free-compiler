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
        "List" <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
        ("nil", "Nil") <- defineTestCon "Nil" 0 "forall a. List a"
        ("cons", "Cons")
          <- defineTestCon "Cons" 2 "forall a . a -> List a -> List a"
        "Forest" <- defineTestTypeSyn "Forest" ["a"] "List (Tree a)"
        "Tree" <- defineTestTypeCon "Tree" 1 ["Leaf", "Branch"]
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
          ++ " (* Normalform instance for Tree *) "
          ++ "Fixpoint nf'Tree__0 {Shape : Type} {Pos : Shape -> Type} "
          ++ "{a_0 b_0 : Type} `{Normalform Shape Pos a_0 b_0} "
          ++ "(x_0 : Tree Shape Pos a_0) "
          ++ ": Free Shape Pos (Tree Identity.Shape Identity.Pos b_0) "
          ++ ":= let fix nf'ListTree__0 {a_1 b_1 : Type} "
          ++ "`{Normalform Shape Pos a_1 b_1} "
          ++ "(x_4 : List Shape Pos (Tree Shape Pos a_1)) "
          ++ ": Free Shape Pos (List Identity.Shape Identity.Pos "
          ++ "(Tree Identity.Shape Identity.Pos b_1)) := match x_4 with "
          ++ "| nil => pure nil "
          ++ "| cons fx_2 fx_3 => fx_2 >>= (fun x_7 => "
          ++ "nf'Tree__0 x_7 >>= (fun nx_2 => "
          ++ "fx_3 >>= (fun x_8 => nf'ListTree__0 x_8 >>= (fun nx_3 => "
          ++ "pure (cons (pure nx_2) (pure nx_3)))))) "
          ++ "end "
          ++ "in match x_0 with "
          ++ "| leaf fx_0 => nf fx_0 >>= (fun nx_0 => pure (leaf (pure nx_0))) "
          ++ "| branch fx_1 => fx_1 >>= (fun x_3 => "
          ++ "nf'ListTree__0 x_3 >>= (fun nx_1 => pure (branch (pure nx_1)))) "
          ++ "end. "
          ++ "Instance NormalformTree__0 {Shape : Type} {Pos : Shape -> Type} "
          ++ "{a_0 b_0 : Type} `{Normalform Shape Pos a_0 b_0} "
          ++ ": Normalform Shape Pos (Tree Shape Pos a_0) "
          ++ "(Tree Identity.Shape Identity.Pos b_0) := { nf' := nf'Tree__0 }. "
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
        ++ " (* Normalform instance for Foo *) "
        ++ "Fixpoint nf'Foo_0 {Shape : Type} {Pos : Shape -> Type} "
        ++ "(x_0 : Foo Shape Pos) "
        ++ ": Free Shape Pos (Foo Identity.Shape Identity.Pos) "
        ++ ":= let 'foo fx_0 fx_1 := x_0 in fx_0 >>= (fun x_1 => "
        ++ "nf'Foo_0 x_1 >>= (fun nx_0 => "
        ++ "fx_1 >>= (fun x_2 => nf'Foo_0 x_2 >>= (fun nx_1 => "
        ++ "pure (foo (pure nx_0) (pure nx_1)))))). "
        ++ "Instance NormalformFoo_0 {Shape : Type} {Pos : Shape -> Type} "
        ++ ": Normalform Shape Pos (Foo Shape Pos) "
        ++ "(Foo Identity.Shape Identity.Pos) := { nf' := nf'Foo_0 }. "
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
            ++ "(* Normalform instance for Foo *) "
            ++ "Fixpoint nf'Foo_0 {Shape : Type} {Pos : Shape -> Type} "
            ++ "(x_0 : Foo Shape Pos) "
            ++ ": Free Shape Pos (Foo Identity.Shape Identity.Pos) "
            ++ ":= match x_0 with "
            ++ "| bar => pure bar "
            ++ "| baz => pure baz "
            ++ "end. "
            ++ "Instance NormalformFoo_0 {Shape : Type} {Pos : Shape -> Type} "
            ++ ": Normalform Shape Pos (Foo Shape Pos) "
            ++ "(Foo Identity.Shape Identity.Pos) := { nf' := nf'Foo_0 }. "
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
          ++ "(* Normalform instance for Foo *) "
          ++ "Fixpoint nf'Foo___0 {Shape : Type} {Pos : Shape -> Type} "
          ++ "{a_0 a_1 b_0 b_1 : Type} `{Normalform Shape Pos a_0 b_0} "
          ++ "`{Normalform Shape Pos a_1 b_1} (x_0 : Foo Shape Pos a_0 a_1) "
          ++ ": Free Shape Pos (Foo Identity.Shape Identity.Pos b_0 b_1) "
          ++ ":= match x_0 with "
          ++ "| bar fx_0 => nf fx_0 >>= "
          ++ "(fun nx_0 => pure (bar (pure nx_0))) "
          ++ "| baz fx_1 => "
          ++ "nf fx_1 >>= (fun nx_1 => pure (baz (pure nx_1))) "
          ++ "end. "
          ++ "Instance NormalformFoo___0 {Shape : Type} {Pos : Shape -> Type} "
          ++ "{a_0 a_1 b_0 b_1 : Type} `{Normalform Shape Pos a_0 b_0} "
          ++ "`{Normalform Shape Pos a_1 b_1} "
          ++ ": Normalform Shape Pos (Foo Shape Pos a_0 a_1) "
          ++ "(Foo Identity.Shape Identity.Pos b_0 b_1) "
          ++ ":= { nf' := nf'Foo___0 }."
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
            ++ "(* Normalform instance for Foo *) "
            ++ "Fixpoint nf'Foo_0 {Shape : Type} {Pos : Shape -> Type} "
            ++ "(x_0 : Foo Shape Pos) "
            ++ ": Free Shape Pos (Foo Identity.Shape Identity.Pos) "
            ++ ":= let 'foo := x_0 in pure foo. "
            ++ "Instance NormalformFoo_0 {Shape : Type} {Pos : Shape -> Type} "
            ++ ": Normalform Shape Pos (Foo Shape Pos) "
            ++ "(Foo Identity.Shape Identity.Pos) "
            ++ ":= { nf' := nf'Foo_0 }."
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
            ++ "(* Normalform instance for Foo *) "
            ++ "Fixpoint nf'Foo__0 {Shape : Type} {Pos : Shape -> Type} "
            ++ "{a_0 b_0 : Type} `{Normalform Shape Pos a_0 b_0} "
            ++ "(x_0 : Foo Shape Pos a_0) "
            ++ ": Free Shape Pos (Foo Identity.Shape Identity.Pos b_0) "
            ++ ":= let 'a fx_0 := x_0 "
            ++ "in nf fx_0 >>= (fun nx_0 => pure (a (pure nx_0))). "
            ++ "Instance NormalformFoo__0 {Shape : Type} {Pos : Shape -> Type} "
            ++ "{a_0 b_0 : Type} `{Normalform Shape Pos a_0 b_0} "
            ++ ": Normalform Shape Pos (Foo Shape Pos a_0) "
            ++ "(Foo Identity.Shape Identity.Pos b_0) "
            ++ ":= { nf' := nf'Foo__0 }."
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
            ++ "(* Normalform instances for Foo, Bar *) "
            ++ "Fixpoint nf'Foo_0 {Shape : Type} {Pos : Shape -> Type} "
            ++ "(x_0 : Foo Shape Pos) "
            ++ ": Free Shape Pos (Foo Identity.Shape Identity.Pos) "
            ++ ":= let 'foo fx_0 := x_0 in fx_0 >>= (fun x_1 => "
            ++ "nf'Bar_0 x_1 >>= (fun nx_0 => pure (foo (pure nx_0)))) "
            ++ "with nf'Bar_0 {Shape : Type} {Pos : Shape -> Type} "
            ++ "(x_0 : Bar Shape Pos) "
            ++ ": Free Shape Pos (Bar Identity.Shape Identity.Pos) "
            ++ ":= let 'bar fx_0 := x_0 in fx_0 >>= (fun x_1 => "
            ++ "nf'Foo_0 x_1 >>= (fun nx_0 => pure (bar (pure nx_0)))). "
            ++ "Instance NormalformFoo_0 {Shape : Type} {Pos : Shape -> Type} "
            ++ ": Normalform Shape Pos (Foo Shape Pos) "
            ++ "(Foo Identity.Shape Identity.Pos) := { nf' := nf'Foo_0 }. "
            ++ "Instance NormalformBar_0 {Shape : Type} {Pos : Shape -> Type} "
            ++ ": Normalform Shape Pos (Bar Shape Pos) "
            ++ "(Bar Identity.Shape Identity.Pos) := { nf' := nf'Bar_0 }."
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
          _ <- defineTestTypeCon "A.Foo1" 0 ["A.Bar1"]
          _ <- defineTestTypeCon "A.Foo2" 0 ["A.Bar2"]
          _ <- defineTestCon "A.Bar1" 1 "A.Foo2 -> A.Foo1"
          _ <- defineTestCon "A.Bar2" 1 "A.Foo1 -> A.Foo2"
          shouldProduceQualifiedNotations
            (Recursive
             ["data A.Foo1 = A.Bar1 A.Foo2", "data A.Foo2 = A.Bar2 A.Foo1"])
            $ "(* Qualified smart constructors for Foo1 *) "
            ++ "Notation \"'A.Bar1' Shape Pos x_0\" := "
            ++ "(@pure Shape Pos (Foo1 Shape Pos) (@bar1 Shape Pos x_0)) "
            ++ "( at level 10, Shape, Pos, x_0 at level 9 ). "
            ++ "Notation \"'@A.Bar1' Shape Pos x_0\" := "
            ++ "(@pure Shape Pos (Foo1 Shape Pos) (@bar1 Shape Pos x_0)) "
            ++ "( only parsing, at level 10, Shape, Pos, x_0 at level 9 ). "
            ++ "(* Qualified smart constructors for Foo2 *) "
            ++ "Notation \"'A.Bar2' Shape Pos x_0\" := "
            ++ "(@pure Shape Pos (Foo2 Shape Pos) (@bar2 Shape Pos x_0)) "
            ++ "( at level 10, Shape, Pos, x_0 at level 9 ). "
            ++ "Notation \"'@A.Bar2' Shape Pos x_0\" := "
            ++ "(@pure Shape Pos (Foo2 Shape Pos) (@bar2 Shape Pos x_0)) "
            ++ "( only parsing, at level 10, Shape, Pos, x_0 at level 9 )."
