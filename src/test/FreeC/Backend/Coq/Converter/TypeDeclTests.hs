-- | This module contains tests for "FreeC.Backend.Coq.Converter.TypeDecl".

module FreeC.Backend.Coq.Converter.TypeDeclTests
  ( testConvertTypeDecl
  , testConvertDataDecls
  )
where

import           Test.Hspec

import           FreeC.Backend.Coq.Converter.TypeDecl
import           FreeC.Backend.Coq.Pretty       ( )
import           FreeC.IR.DependencyGraph
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Test.Parser
import           FreeC.Test.Environment
import           FreeC.Test.Expectations

-------------------------------------------------------------------------------
-- Expectation setters                                                       --
-------------------------------------------------------------------------------

-- | Parses the given type-level IR declarations, converts them to Coq using
--   'convertTypeComponent' and sets the expectation that the resulting AST
--   is equal to the given output when pretty printed modulo white
--   space.
shouldConvertTypeDeclsTo
  :: DependencyComponent String -> String -> Converter Expectation
shouldConvertTypeDeclsTo inputStrs expectedOutputStr = do
  input  <- parseTestComponent inputStrs
  output <- convertTypeComponent input
  return (output `prettyShouldBe` expectedOutputStr)

-------------------------------------------------------------------------------
-- Tests for Type Synonym Declarations                                       --
-------------------------------------------------------------------------------

-- | Test group for 'convertTypeSynDecl' tests.
testConvertTypeDecl :: Spec
testConvertTypeDecl =
  describe "FreeC.Backend.Coq.Converter.TypeDecl.convertTypeSynDecl" $ do
    it "translates non-polymorphic type synonyms correctly"
      $ shouldSucceedWith
      $ do
          "Integer" <- defineTestTypeCon "Integer" 0 []
          "List"    <- defineTestTypeCon "List" 1 []
          "TermPos" <- defineTestTypeSyn "TermPos" [] "List Integer"
          shouldConvertTypeDeclsTo (NonRecursive "type TermPos = List Integer")
            $  "Definition TermPos (Shape : Type) (Pos : Shape -> Type)"
            ++ "  : Type"
            ++ " := List Shape Pos (Integer Shape Pos)."

    it "translates polymorphic type synonyms correctly" $ shouldSucceedWith $ do
      "List"  <- defineTestTypeCon "List" 1 []
      "Pair"  <- defineTestTypeCon "Pair" 2 []
      "Queue" <- defineTestTypeSyn "Queue" ["a"] "Pair (List a) (List a)"
      shouldConvertTypeDeclsTo
          (NonRecursive "type Queue a = Pair (List a) (List a)")
        $  "Definition Queue (Shape : Type) (Pos : Shape -> Type)"
        ++ "  (a : Type) : Type"
        ++ " := Pair Shape Pos (List Shape Pos a) (List Shape Pos a)."

    it "expands type synonyms in mutually recursive data type declarations"
      $ shouldSucceedWith
      $ do
          "List"               <- defineTestTypeCon "List" 1 []
          "Forest" <- defineTestTypeSyn "Forest" ["a"] "List (Tree a)"
          "Tree"               <- defineTestTypeCon "Tree" 1 []
          ("leaf"  , "Leaf"  ) <- defineTestCon "Leaf" 1 "forall a. a -> Tree a"
          ("branch", "Branch") <- defineTestCon "Branch"
                                                1
                                                "forall a. Forest a -> Tree a"
          shouldConvertTypeDeclsTo
              (Recursive
                [ "type Forest a = List (Tree a)"
                , "data Tree a = Leaf a | Branch (Forest a)"
                ]
              )
            $  "(* Data type declarations for Tree *) "
            ++ "Inductive Tree (Shape : Type) (Pos : Shape -> Type) (a : Type)"
            ++ " : Type"
            ++ " := leaf : Free Shape Pos a -> Tree Shape Pos a"
            ++ " |  branch : Free Shape Pos (List Shape Pos (Tree Shape Pos a))"
            ++ "              -> Tree Shape Pos a. "
            ++ "(* Arguments sentences for Tree *) "
            ++ "Arguments leaf {Shape} {Pos} {a}. "
            ++ "Arguments branch {Shape} {Pos} {a}. "
            ++ "(* Induction scheme for Tree *) "
            ++ "Definition Tree_Ind (Shape : Type) (Pos : Shape -> Type) "
            ++ "  (a : Type) (x_0 : Tree Shape Pos a -> Prop) "
            ++ "  (x_2 : forall (x_1 : Free Shape Pos a), x_0 (leaf x_1)) "
            ++ "  (x_4 : forall "
            ++ "   (x_3 : Free Shape Pos (List Shape Pos (Tree Shape Pos a))),"
            ++ "    x_0 (branch x_3)) "
            ++ " : forall (x_5 : Tree Shape Pos a), x_0 x_5. "
            ++ "Proof. fix H 1; intro; prove_ind. Defined. "
            ++ "(* Smart constructors for Tree *) "
            ++ "Definition Leaf (Shape : Type) (Pos : Shape -> Type)"
            ++ "  {a : Type}"
            ++ "  (x_0 : Free Shape Pos a)"
            ++ " : Free Shape Pos (Tree Shape Pos a) := pure (leaf x_0). "
            ++ "Definition Branch (Shape : Type) (Pos : Shape -> Type)"
            ++ "  {a : Type}"
            ++ "  (x_0 : Free Shape Pos (List Shape Pos (Tree Shape Pos a)))"
            ++ " : Free Shape Pos (Tree Shape Pos a) := pure (branch x_0). "
            ++ "Definition Forest (Shape : Type) (Pos : Shape -> Type)"
            ++ "  (a : Type)"
            ++ " : Type"
            ++ " := List Shape Pos (Tree Shape Pos a)."

    it "sorts type synonym declarations topologically" $ shouldSucceedWith $ do
      "Bar"           <- defineTestTypeSyn "Bar" [] "Baz"
      "Baz"           <- defineTestTypeSyn "Baz" [] "Foo"
      "Foo"           <- defineTestTypeCon "Foo" 1 ["Foo"]
      ("foo", "Foo0") <- defineTestCon "Foo" 2 "Bar -> Baz -> Foo"
      shouldConvertTypeDeclsTo
          (Recursive
            ["type Bar = Baz", "type Baz = Foo", "data Foo = Foo Bar Baz"]
          )
        $  "(* Data type declarations for Foo *) "
        ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type)"
        ++ " : Type"
        ++ " := foo : Free Shape Pos (Foo Shape Pos)"
        ++ "          -> Free Shape Pos (Foo Shape Pos)"
        ++ "          -> Foo Shape Pos. "
        ++ "(* Arguments sentences for Foo *) "
        ++ "Arguments foo {Shape} {Pos}. "
        ++ "(* Induction scheme for Foo *) "
        ++ "Definition Foo_Ind (Shape : Type) (Pos : Shape -> Type) "
        ++ "  (x_0 : Foo Shape Pos -> Prop) "
        ++ "  (x_3 : forall (x_1 : Free Shape Pos (Foo Shape Pos)) "
        ++ "  (x_2 : Free Shape Pos (Foo Shape Pos)), "
        ++ "    ForFree Shape Pos (Foo Shape Pos) x_0 x_1 -> "
        ++ "    ForFree Shape Pos (Foo Shape Pos) x_0 x_2 -> "
        ++ "    x_0 (foo x_1 x_2)) "
        ++ " : forall (x_4 : Foo Shape Pos), x_0 x_4. "
        ++ "Proof. fix H 1; intro; prove_ind. Defined. "
        ++ "(* Smart constructors for Foo *) "
        ++ "Definition Foo0 (Shape : Type) (Pos : Shape -> Type)"
        ++ "  (x_0 : Free Shape Pos (Foo Shape Pos))"
        ++ "  (x_1 : Free Shape Pos (Foo Shape Pos))"
        ++ " : Free Shape Pos (Foo Shape Pos)"
        ++ " := pure (foo x_0 x_1). "
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
-- Data type declarations                                                    --
-------------------------------------------------------------------------------

-- | Test group for 'convertDataDecls' tests.
testConvertDataDecls :: Spec
testConvertDataDecls =
  describe "FreeC.Backend.Coq.Converter.TypeDecl.convertDataDecls" $ do
    it "translates non-polymorphic data types correctly"
      $ shouldSucceedWith
      $ do
          "Foo"          <- defineTestTypeCon "Foo" 0 ["Bar", "Baz"]
          ("bar", "Bar") <- defineTestCon "Bar" 0 "Foo"
          ("baz", "Baz") <- defineTestCon "Baz" 0 "Foo"
          shouldConvertTypeDeclsTo (NonRecursive "data Foo = Bar | Baz")
            $  "(* Data type declarations for Foo *) "
            ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type) : Type "
            ++ " := bar : Foo Shape Pos "
            ++ " |  baz : Foo Shape Pos. "
            ++ "(* Arguments sentences for Foo *) "
            ++ "Arguments bar {Shape} {Pos}. "
            ++ "Arguments baz {Shape} {Pos}. "
            ++ "(* Induction scheme for Foo *) "
            ++ "Definition Foo_Ind (Shape : Type) (Pos : Shape -> Type) "
            ++ "  (x_0 : Foo Shape Pos -> Prop) "
            ++ "  (x_1 : x_0 bar) "
            ++ "  (x_2 : x_0 baz) "
            ++ " : forall (x_3 : Foo Shape Pos), x_0 x_3. "
            ++ "Proof. fix H 1; intro; prove_ind. Defined. "
            ++ "(* Smart constructors for Foo *) "
            ++ "Definition Bar (Shape : Type) (Pos : Shape -> Type) "
            ++ " : Free Shape Pos (Foo Shape Pos) := pure bar. "
            ++ "Definition Baz (Shape : Type) (Pos : Shape -> Type) "
            ++ " : Free Shape Pos (Foo Shape Pos) := pure baz."

    it "translates polymorphic data types correctly" $ shouldSucceedWith $ do
      "Foo"          <- defineTestTypeCon "Foo" 2 ["Bar", "Baz"]
      ("bar", "Bar") <- defineTestCon "Bar" 1 "forall a b. a -> Foo a b"
      ("baz", "Baz") <- defineTestCon "Baz" 1 "forall a b. b -> Foo a b"
      shouldConvertTypeDeclsTo (NonRecursive "data Foo a b = Bar a | Baz b")
        $  "(* Data type declarations for Foo *) "
        ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type) "
        ++ " (a b : Type) : Type "
        ++ " := bar : Free Shape Pos a -> Foo Shape Pos a b "
        ++ " |  baz : Free Shape Pos b -> Foo Shape Pos a b. "
        ++ "(* Arguments sentences for Foo *) "
        ++ "Arguments bar {Shape} {Pos} {a} {b}. "
        ++ "Arguments baz {Shape} {Pos} {a} {b}. "
        ++ "(* Induction scheme for Foo *) "
        ++ "Definition Foo_Ind (Shape : Type) (Pos : Shape -> Type) "
        ++ "  (a b : Type) (x_0 : Foo Shape Pos a b -> Prop) "
        ++ "  (x_2 : forall (x_1 : Free Shape Pos a), x_0 (bar x_1)) "
        ++ "  (x_4 : forall (x_3 : Free Shape Pos b), x_0 (baz x_3)) "
        ++ " : forall (x_5 : Foo Shape Pos a b), x_0 x_5. "
        ++ "Proof. fix H 1; intro; prove_ind. Defined. "
        ++ "(* Smart constructors for Foo *) "
        ++ "Definition Bar (Shape : Type) (Pos : Shape -> Type) "
        ++ " {a b : Type} (x_0 : Free Shape Pos a) "
        ++ " : Free Shape Pos (Foo Shape Pos a b) := pure (bar x_0). "
        ++ "Definition Baz (Shape : Type) (Pos : Shape -> Type) "
        ++ " {a b : Type} (x_0 : Free Shape Pos b) "
        ++ " : Free Shape Pos (Foo Shape Pos a b) := pure (baz x_0)."

    it "renames constructors with same name as their data type"
      $ shouldSucceedWith
      $ do
          "Foo"           <- defineTestTypeCon "Foo" 0 ["Foo"]
          ("foo", "Foo0") <- defineTestCon "Foo" 0 "Foo"
          shouldConvertTypeDeclsTo (NonRecursive "data Foo = Foo")
            $  "(* Data type declarations for Foo *) "
            ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type) : Type "
            ++ " := foo : Foo Shape Pos. "
            ++ "(* Arguments sentences for Foo *) "
            ++ "Arguments foo {Shape} {Pos}. "
            ++ "(* Induction scheme for Foo *) "
            ++ "Definition Foo_Ind (Shape : Type) (Pos : Shape -> Type) "
            ++ "  (x_0 : Foo Shape Pos -> Prop) "
            ++ "  (x_1 : x_0 foo) "
            ++ " : forall (x_2 : Foo Shape Pos), x_0 x_2. "
            ++ "Proof. fix H 1; intro; prove_ind. Defined. "
            ++ "(* Smart constructors for Foo *) "
            ++ "Definition Foo0 (Shape : Type) (Pos : Shape -> Type) "
            ++ " : Free Shape Pos (Foo Shape Pos) := pure foo."

    it "renames type variables with same name as generated constructors"
      $ shouldSucceedWith
      $ do
          "Foo"      <- defineTestTypeCon "Foo" 0 ["A"]
          ("a", "A") <- defineTestCon "A" 1 "forall a. a -> Foo a"
          shouldConvertTypeDeclsTo (NonRecursive "data Foo a = A a")
            $  "(* Data type declarations for Foo *) "
            ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type) "
            ++ " (a0 : Type) : Type "
            ++ " := a : Free Shape Pos a0 -> Foo Shape Pos a0. "
            ++ "(* Arguments sentences for Foo *) "
            ++ "Arguments a {Shape} {Pos} {a0}. "
            ++ "(* Induction scheme for Foo *) "
            ++ "Definition Foo_Ind (Shape : Type) (Pos : Shape -> Type) "
            ++ "  (a0 : Type) (x_0 : Foo Shape Pos a0 -> Prop) "
            ++ "  (x_2 : forall (x_1 : Free Shape Pos a0), x_0 (a x_1)) "
            ++ " : forall (x_3 : Foo Shape Pos a0), x_0 x_3. "
            ++ "Proof. fix H 1; intro; prove_ind. Defined. "
            ++ "(* Smart constructors for Foo *) "
            ++ "Definition A (Shape : Type) (Pos : Shape -> Type) "
            ++ " {a0 : Type} (x_0 : Free Shape Pos a0) "
            ++ " : Free Shape Pos (Foo Shape Pos a0) := pure (a x_0)."

    it "translates mutually recursive data types correctly"
      $ shouldSucceedWith
      $ do
          "Foo"           <- defineTestTypeCon "Foo" 0 ["Foo"]
          ("foo", "Foo0") <- defineTestCon "Foo" 1 "Bar -> Foo"
          "Bar"           <- defineTestTypeCon "Bar" 0 ["Bar"]
          ("bar", "Bar0") <- defineTestCon "Bar" 1 "Foo -> Bar"
          shouldConvertTypeDeclsTo
              (Recursive ["data Foo = Foo Bar", "data Bar = Bar Foo"])
            $  "(* Data type declarations for Foo, Bar *) "
            ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type) : Type"
            ++ "  := foo : Free Shape Pos (Bar Shape Pos) -> Foo Shape Pos "
            ++ "with Bar (Shape : Type) (Pos : Shape -> Type) : Type"
            ++ "  := bar : Free Shape Pos (Foo Shape Pos) -> Bar Shape Pos. "
            ++ "(* Arguments sentences for Foo *) "
            ++ "Arguments foo {Shape} {Pos}. "
            ++ "(* Induction scheme for Foo *) "
            ++ "Definition Foo_Ind (Shape : Type) (Pos : Shape -> Type) "
            ++ "  (x_0 : Foo Shape Pos -> Prop) "
            ++ "  (x_2 : forall (x_1 : Free Shape Pos (Bar Shape Pos)), "
            ++ "           x_0 (foo x_1)) "
            ++ " : forall (x_3 : Foo Shape Pos), x_0 x_3. "
            ++ "Proof. fix H 1; intro; prove_ind. Defined. "
            ++ "(* Smart constructors for Foo *) "
            ++ "Definition Foo0 (Shape : Type) (Pos : Shape -> Type)"
            ++ "  (x_0 : Free Shape Pos (Bar Shape Pos))"
            ++ "  : Free Shape Pos (Foo Shape Pos)"
            ++ "  := pure (foo x_0). "
            ++ "(* Arguments sentences for Bar *) "
            ++ "Arguments bar {Shape} {Pos}. "
            ++ "(* Induction scheme for Bar *) "
            ++ "Definition Bar_Ind (Shape : Type) (Pos : Shape -> Type) "
            ++ "  (x_0 : Bar Shape Pos -> Prop) "
            ++ "  (x_2 : forall (x_1 : Free Shape Pos (Foo Shape Pos)), "
            ++ "           x_0 (bar x_1)) "
            ++ " : forall (x_3 : Bar Shape Pos), x_0 x_3. "
            ++ "Proof. fix H 1; intro; prove_ind. Defined. "
            ++ "(* Smart constructors for Bar *) "
            ++ "Definition Bar0 (Shape : Type) (Pos : Shape -> Type)"
            ++ "  (x_0 : Free Shape Pos (Foo Shape Pos))"
            ++ "  : Free Shape Pos (Bar Shape Pos)"
            ++ "  := pure (bar x_0)."

    it "creates a correct induction scheme" $ shouldSucceedWith $ do
      "Foo"           <- defineTestTypeCon "Foo" 1 ["Foo"]
      ("foo", "Foo0") <- defineTestCon
        "Foo"
        3
        "forall a. Foo a -> a -> Foo a -> Foo a"
      shouldConvertTypeDeclsTo
          (Recursive ["data Foo a = Foo (Foo a) a (Foo a)"])
        $  "(* Data type declarations for Foo *) "
        ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type) (a : Type) "
        ++ "  : Type"
        ++ "  := foo : Free Shape Pos (Foo Shape Pos a) -> "
        ++ "           Free Shape Pos a -> "
        ++ "           Free Shape Pos (Foo Shape Pos a) -> "
        ++ "             Foo Shape Pos a. "
        ++ "(* Arguments sentences for Foo *) "
        ++ "Arguments foo {Shape} {Pos} {a}. "
        ++ "(* Induction scheme for Foo *) "
        ++ "Definition Foo_Ind (Shape : Type) (Pos : Shape -> Type) "
        ++ "  (a : Type) (x_0 : Foo Shape Pos a -> Prop) "
        ++ "  (x_4 : forall "
        ++ "           (x_1 : Free Shape Pos (Foo Shape Pos a)) "
        ++ "           (x_2 : Free Shape Pos a) "
        ++ "           (x_3 : Free Shape Pos (Foo Shape Pos a)), "
        ++ "         ForFree Shape Pos (Foo Shape Pos a) x_0 x_1 -> "
        ++ "         ForFree Shape Pos (Foo Shape Pos a) x_0 x_3 -> "
        ++ "           x_0 (foo x_1 x_2 x_3)) "
        ++ " : forall (x_5 : Foo Shape Pos a), x_0 x_5. "
        ++ "Proof. fix H 1; intro; prove_ind. Defined. "
        ++ "(* Smart constructors for Foo *) "
        ++ "Definition Foo0 (Shape : Type) (Pos : Shape -> Type) {a : Type} "
        ++ "  (x_0 : Free Shape Pos (Foo Shape Pos a)) "
        ++ "  (x_1 : Free Shape Pos a) "
        ++ "  (x_2 : Free Shape Pos (Foo Shape Pos a)) "
        ++ "  : Free Shape Pos (Foo Shape Pos a)"
        ++ "  := pure (foo x_0 x_1 x_2). "
