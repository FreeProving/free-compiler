module Compiler.Converter.TypeDeclTests where

import           Test.Hspec

import           Compiler.Util.Test

-------------------------------------------------------------------------------
-- Type synonym declarations                                                 --
-------------------------------------------------------------------------------

-- | Test group for 'convertTypeDecl' tests.
testConvertTypeDecl :: Spec
testConvertTypeDecl =
  describe "Compiler.Converter.TypeDecl.convertTypeDecl" $ do
    it "translates non-polymorphic type synonyms correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo ["type TermPos = [Int]"]
            $  "Definition TermPos (Shape : Type) (Pos : Shape -> Type)"
            ++ "  : Type"
            ++ " := List Shape Pos (Int Shape Pos)."

    it "translates polymorphic type synonyms correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo ["type Queue a = ([a], [a])"]
            $  "Definition Queue (Shape : Type) (Pos : Shape -> Type)"
            ++ "  (a : Type) : Type"
            ++ " := Pair Shape Pos (List Shape Pos a) (List Shape Pos a)."

    it "expands function type synonyms correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "String"       <- defineTestTypeCon "String" 0
          "Expr"         <- defineTestTypeCon "Expr" 0
          ("var", "Var") <- defineTestCon "Var" 1 "String -> Expr"
          shouldTranslateDeclsTo
              [ "type Subst = String -> Expr"
              , "identity :: Subst"
              , "identity s = Var s"
              ]
            $  "Definition Subst (Shape : Type) (Pos : Shape -> Type) : Type"
            ++ " := Free Shape Pos (String Shape Pos)"
            ++ "    -> Free Shape Pos (Expr Shape Pos). "
            ++ "Definition identity (Shape : Type) (Pos : Shape -> Type)"
            ++ "  (s : Free Shape Pos (String Shape Pos))"
            ++ " : Free Shape Pos (Expr Shape Pos)"
            ++ " := Var Shape Pos s."

    it "expands type synonyms in mutually recursive data type declarations"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo
              [ "type Forest a = [Tree a]"
              , "data Tree a = Leaf a | Branch (Forest a)"
              ]
            $  "(* Data type declarations for Tree *) "
            ++ "Inductive Tree (Shape : Type) (Pos : Shape -> Type) (a : Type)"
            ++ " : Type"
            ++ " := leaf : Free Shape Pos a -> Tree Shape Pos a"
            ++ " |  branch : Free Shape Pos (List Shape Pos (Tree Shape Pos a))"
            ++ "              -> Tree Shape Pos a. "
            ++ "(* Arguments sentences for Tree *) "
            ++ "Arguments leaf {Shape} {Pos} {a}. "
            ++ "Arguments branch {Shape} {Pos} {a}. "
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

    it "sorts type synonym declarations topologically"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo
              ["type Bar = Baz", "type Baz = Foo", "data Foo = Foo Bar Baz"]
            $  "(* Data type declarations for Foo *) "
            ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type)"
            ++ " : Type"
            ++ " := foo : Free Shape Pos (Foo Shape Pos)"
            ++ "          -> Free Shape Pos (Foo Shape Pos)"
            ++ "          -> Foo Shape Pos. "
            ++ "(* Arguments sentences for Foo *) "
            ++ "Arguments foo {Shape} {Pos}. "
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

    it "fails if type synonyms form a cycle"
      $ shouldReportFatal
      $ fromConverter
      $ convertTestDecls ["type Foo = Bar", "type Bar = Baz"]



-------------------------------------------------------------------------------
-- Data type declarations                                                    --
-------------------------------------------------------------------------------

-- | Test group for 'convertDataDecls' tests.
testConvertDataDecls :: Spec
testConvertDataDecls =
  describe "Compiler.Converter.TypeDecl.convertDataDecls" $ do
    it "translates non-polymorphic data types correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo ["data Foo = Bar | Baz"]
            $  "(* Data type declarations for Foo *) "
            ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type) : Type "
            ++ " := bar : Foo Shape Pos "
            ++ " |  baz : Foo Shape Pos. "
            ++ "(* Arguments sentences for Foo *) "
            ++ "Arguments bar {Shape} {Pos}. "
            ++ "Arguments baz {Shape} {Pos}. "
            ++ "(* Smart constructors for Foo *) "
            ++ "Definition Bar (Shape : Type) (Pos : Shape -> Type) "
            ++ " : Free Shape Pos (Foo Shape Pos) := pure bar. "
            ++ "Definition Baz (Shape : Type) (Pos : Shape -> Type) "
            ++ " : Free Shape Pos (Foo Shape Pos) := pure baz."

    it "translates polymorphic data types correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo ["data Foo a b = Bar a | Baz b"]
            $  "(* Data type declarations for Foo *) "
            ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type) "
            ++ " (a b : Type) : Type "
            ++ " := bar : Free Shape Pos a -> Foo Shape Pos a b "
            ++ " |  baz : Free Shape Pos b -> Foo Shape Pos a b. "
            ++ "(* Arguments sentences for Foo *) "
            ++ "Arguments bar {Shape} {Pos} {a} {b}. "
            ++ "Arguments baz {Shape} {Pos} {a} {b}. "
            ++ "(* Smart constructors for Foo *) "
            ++ "Definition Bar (Shape : Type) (Pos : Shape -> Type) "
            ++ " {a b : Type} (x_0 : Free Shape Pos a) "
            ++ " : Free Shape Pos (Foo Shape Pos a b) := pure (bar x_0). "
            ++ "Definition Baz (Shape : Type) (Pos : Shape -> Type) "
            ++ " {a b : Type} (x_0 : Free Shape Pos b) "
            ++ " : Free Shape Pos (Foo Shape Pos a b) := pure (baz x_0)."

    it "renames constructors with same name as their data type"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo ["data Foo = Foo"]
            $  "(* Data type declarations for Foo *) "
            ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type) : Type "
            ++ " := foo : Foo Shape Pos. "
            ++ "(* Arguments sentences for Foo *) "
            ++ "Arguments foo {Shape} {Pos}. "
            ++ "(* Smart constructors for Foo *) "
            ++ "Definition Foo0 (Shape : Type) (Pos : Shape -> Type) "
            ++ " : Free Shape Pos (Foo Shape Pos) := pure foo."

    it "renames type variables with same name as constructors"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo ["data Foo a = A a"]
            $  "(* Data type declarations for Foo *) "
            ++ "Inductive Foo (Shape : Type) (Pos : Shape -> Type) "
            ++ " (a0 : Type) : Type "
            ++ " := a : Free Shape Pos a0 -> Foo Shape Pos a0. "
            ++ "(* Arguments sentences for Foo *) "
            ++ "Arguments a {Shape} {Pos} {a0}. "
            ++ "(* Smart constructors for Foo *) "
            ++ "Definition A (Shape : Type) (Pos : Shape -> Type) "
            ++ " {a0 : Type} (x_0 : Free Shape Pos a0) "
            ++ " : Free Shape Pos (Foo Shape Pos a0) := pure (a x_0)."

    it "translates mutually recursive data types correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo ["data Foo = Foo Bar", "data Bar = Bar Foo"]
            $  "(* Data type declarations for Bar, Foo *) "
            ++ "Inductive Bar (Shape : Type) (Pos : Shape -> Type) : Type"
            ++ "  := bar : Free Shape Pos (Foo Shape Pos) -> Bar Shape Pos "
            ++ "with Foo (Shape : Type) (Pos : Shape -> Type) : Type"
            ++ "  := foo : Free Shape Pos (Bar Shape Pos) -> Foo Shape Pos. "
            ++ "(* Arguments sentences for Bar *) "
            ++ "Arguments bar {Shape} {Pos}. "
            ++ "(* Smart constructors for Bar *) "
            ++ "Definition Bar0 (Shape : Type) (Pos : Shape -> Type)"
            ++ "  (x_0 : Free Shape Pos (Foo Shape Pos))"
            ++ "  : Free Shape Pos (Bar Shape Pos)"
            ++ "  := pure (bar x_0). "
            ++ "(* Arguments sentences for Foo *) "
            ++ "Arguments foo {Shape} {Pos}. "
            ++ "(* Smart constructors for Foo *) "
            ++ "Definition Foo0 (Shape : Type) (Pos : Shape -> Type)"
            ++ "  (x_0 : Free Shape Pos (Bar Shape Pos))"
            ++ "  : Free Shape Pos (Foo Shape Pos)"
            ++ "  := pure (foo x_0)."
