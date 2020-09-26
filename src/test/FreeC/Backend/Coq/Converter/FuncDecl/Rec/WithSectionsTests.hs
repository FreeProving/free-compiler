-- | This module contains tests for
--   "FreeC.Backend.Coq.Converter.FuncDecl.Rec.WithSections".
module FreeC.Backend.Coq.Converter.FuncDecl.Rec.WithSectionsTests
  ( testConvertRecFuncDeclWithSections
  ) where

import           Test.Hspec

import           FreeC.Backend.Coq.Analysis.ConstantArguments
import           FreeC.Backend.Coq.Converter.FuncDecl.Rec.WithSections
import           FreeC.Backend.Coq.Pretty                              ()
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Test.Environment
import           FreeC.Test.Expectations
import           FreeC.Test.Parser

-------------------------------------------------------------------------------
-- Expectation Setters                                                       --
-------------------------------------------------------------------------------
-- | Parses the given function declarations, converts them to Coq using
--   'convertRecFuncDeclsWithSection' and expects the resulting Coq code
--   to equal the given expected output modulo whitespace.
convertRecFuncDeclsWithSectionTo :: [String] -> String -> Converter Expectation
convertRecFuncDeclsWithSectionTo inputStrs expectedOutputStr = do
  input <- mapM parseTestFuncDecl inputStrs
  constArgs <- identifyConstArgs input
  output <- convertRecFuncDeclsWithSection constArgs input
  return (output `prettyShouldBe` expectedOutputStr)

-------------------------------------------------------------------------------
-- Tests                                                                     --
-------------------------------------------------------------------------------
-- | Test group for 'convertRecFuncDeclsWithSection' tests.
testConvertRecFuncDeclWithSections :: Spec
testConvertRecFuncDeclWithSections = context "with section sentences" $ do
  it "creates variable sentences for constant arguments" $ shouldSucceedWith $ do
    "List" <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
    ("nil", "Nil") <- defineTestCon "Nil" 0 "forall a. List a"
    ("cons", "Cons") <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
    "map" <- defineTestFunc "map" 2 "forall a b. (a -> b) -> List a -> List b"
    convertRecFuncDeclsWithSectionTo
      [ "map @a @b (f :: a -> b) (xs :: List a) :: List b"
          ++ "  = case xs of {"
          ++ "      Nil        -> Nil @b;"
          ++ "      Cons x xs' -> Cons @b (f x) (map @a @b f xs')"
          ++ "    }"
      ]
      $ "Section section_map. "
      ++ "(* Constant arguments for map *) "
      ++ "Variable Shape : Type. "
      ++ "Variable Pos : Shape -> Type. "
      ++ "Variable a b : Type. "
      ++ "Variable f : Free Shape Pos"
      ++ "  (Free Shape Pos a -> Free Shape Pos b). "
      ++ "(* Helper functions for map *) "
      ++ "Fixpoint map1 (xs : List Shape Pos a) {struct xs}"
      ++ "  := match xs with"
      ++ "     | nil            => @Nil Shape Pos b"
      ++ "     | cons x xs' =>"
      ++ "        @Cons Shape Pos b"
      ++ "          (f >>= (fun f0 => f0 x))"
      ++ "          (xs' >>= (fun (xs'0 : List Shape Pos a) =>"
      ++ "             map1 xs'0))"
      ++ "     end. "
      ++ "(* Main functions for map *) "
      ++ "Definition map0 (xs : Free Shape Pos (List Shape Pos a))"
      ++ "  : Free Shape Pos (List Shape Pos b)"
      ++ "  := xs >>= (fun (xs0 : List Shape Pos a) => map1 xs0). "
      ++ "End section_map. "
      ++ "Definition map (Shape : Type) (Pos : Shape -> Type)"
      ++ "  {a b : Type}"
      ++ "  (f : Free Shape Pos (Free Shape Pos a -> Free Shape Pos b))"
      ++ "  (xs : Free Shape Pos (List Shape Pos a))"
      ++ "  : Free Shape Pos (List Shape Pos b)"
      ++ "  := map0 Shape Pos a b f xs."
  it "creates variable sentences for type variables in constant argument types"
    $ shouldSucceedWith
    $ do
      "List" <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
      ("nil", "Nil") <- defineTestCon "Nil" 0 "forall a. List a"
      ("cons", "Cons")
        <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
      "mapAlt"
        <- defineTestFunc "mapAlt" 2 "forall a b. (a -> b) -> List a -> List b"
      "mapAlt'"
        <- defineTestFunc "mapAlt'" 2 "forall a b. (a -> b) -> List a -> List b"
      convertRecFuncDeclsWithSectionTo
        [ "mapAlt @a @b (f :: a -> b) (xs :: List a) :: List b"
            ++ "  = case xs of {"
            ++ "    Nil        -> Nil @b;"
            ++ "    Cons x xs' -> Cons @b (f x) (mapAlt' @a @b f xs')"
            ++ "  }"
        , "mapAlt' @b @a (f :: b -> a) (xs :: List b) :: List a"
            ++ "  = case xs of {"
            ++ "      Nil        -> Nil @a;"
            ++ "      Cons x xs' -> Cons @a (f x) (mapAlt @a @b f xs')"
            ++ "    }"
        ]
        $ "Section section_mapAlt_mapAlt'. "
        ++ "(* Constant arguments for mapAlt, mapAlt' *) "
        ++ "Variable Shape : Type. "
        ++ "Variable Pos : Shape -> Type. "
        ++ "Variable a b : Type. "
        ++ "Variable f : Free Shape Pos"
        ++ "  (Free Shape Pos a -> Free Shape Pos b). "
        ++ "(* Helper functions for mapAlt, mapAlt' *) "
        ++ "Fixpoint mapAlt1 (xs : List Shape Pos a) {struct xs}"
        ++ "  := match xs with"
        ++ "     | nil            => @Nil Shape Pos b"
        ++ "     | cons x xs' =>"
        ++ "        @Cons Shape Pos b"
        ++ "          (f >>= (fun f0 => f0 x))"
        ++ "          (xs' >>= (fun (xs'0 : List Shape Pos a) =>"
        ++ "             mapAlt'1 xs'0))"
        ++ "     end"
        ++ " with mapAlt'1 (xs : List Shape Pos a) {struct xs}"
        ++ "  := match xs with"
        ++ "     | nil            => @Nil Shape Pos b"
        ++ "     | cons x xs' =>"
        ++ "        @Cons Shape Pos b"
        ++ "          (f >>= (fun f0 => f0 x))"
        ++ "          (xs' >>= (fun (xs'0 : List Shape Pos a) =>"
        ++ "             mapAlt1 xs'0))"
        ++ "     end. "
        ++ "(* Main functions for mapAlt, mapAlt' *) "
        ++ "Definition mapAlt0 (xs : Free Shape Pos (List Shape Pos a))"
        ++ "  : Free Shape Pos (List Shape Pos b)"
        ++ "  := xs >>= (fun (xs0 : List Shape Pos a) => mapAlt1 xs0). "
        ++ "Definition mapAlt'0 (xs : Free Shape Pos (List Shape Pos a))"
        ++ "  : Free Shape Pos (List Shape Pos b)"
        ++ "  := xs >>= (fun (xs0 : List Shape Pos a) => mapAlt'1 xs0). "
        ++ "End section_mapAlt_mapAlt'. "
        ++ "Definition mapAlt (Shape : Type) (Pos : Shape -> Type)"
        ++ "  {a b : Type}"
        ++ "  (f : Free Shape Pos (Free Shape Pos a -> Free Shape Pos b))"
        ++ "  (xs : Free Shape Pos (List Shape Pos a))"
        ++ "  : Free Shape Pos (List Shape Pos b)"
        ++ "  := mapAlt0 Shape Pos a b f xs. "
        ++ "Definition mapAlt' (Shape : Type) (Pos : Shape -> Type)"
        ++ "  {b a : Type}"
        ++ "  (f : Free Shape Pos (Free Shape Pos b -> Free Shape Pos a))"
        ++ "  (xs : Free Shape Pos (List Shape Pos b))"
        ++ "  : Free Shape Pos (List Shape Pos a)"
        ++ "  := mapAlt'0 Shape Pos b a f xs."
  it "does not create variable sentences for unused constant arguments"
    $ shouldSucceedWith
    $ do
      "List" <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
      ("nil", "Nil") <- defineTestCon "Nil" 0 "forall a. List a"
      ("cons", "Cons")
        <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
      "foo" <- defineTestFunc "foo" 3 "forall a. a -> a -> List a -> List a"
      convertRecFuncDeclsWithSectionTo
        [ "foo @a (u :: a) (v :: a) (xs :: List a) :: List a"
            ++ "  = case xs of {"
            ++ "      Nil -> Nil @a;"
            ++ "      Cons x xs' -> Cons @a v (foo @a u v xs')"
            ++ "    }"
        ]
        $ "Section section_foo. "
        ++ "(* Constant arguments for foo *) "
        ++ "Variable Shape : Type. "
        ++ "Variable Pos : Shape -> Type. "
        ++ "Variable a : Type. "
        ++ "Variable v : Free Shape Pos a. "
        ++ "(* Helper functions for foo *) "
        ++ "Fixpoint foo1 (xs : List Shape Pos a) {struct xs}"
        ++ "  := match xs with"
        ++ "     | nil            => @Nil Shape Pos a"
        ++ "     | cons x xs' =>"
        ++ "        @Cons Shape Pos a v"
        ++ "          (xs' >>= (fun (xs'0 : List Shape Pos a) =>"
        ++ "              foo1 xs'0))"
        ++ "     end. "
        ++ "(* Main functions for foo *) "
        ++ "Definition foo0 (xs : Free Shape Pos (List Shape Pos a))"
        ++ "  : Free Shape Pos (List Shape Pos a)"
        ++ "  := xs >>= (fun (xs0 : List Shape Pos a) => foo1 xs0). "
        ++ "End section_foo. "
        ++ "Definition foo (Shape : Type) (Pos : Shape -> Type)"
        ++ "  {a : Type}"
        ++ "  (u : Free Shape Pos a)"
        ++ "  (v : Free Shape Pos a)"
        ++ "  (xs : Free Shape Pos (List Shape Pos a))"
        ++ "  : Free Shape Pos (List Shape Pos a)"
        ++ "  := foo0 Shape Pos a v xs."
  it "passes constant type arguments explicitly the main function"
    $ shouldSucceedWith
    $ do
      "List" <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
      ("nil", "Nil") <- defineTestCon "Nil" 0 "forall a. List a"
      ("cons", "Cons")
        <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
      "foo" <- defineTestFunc "foo" 3 "forall a b c. a -> b -> List c -> List b"
      convertRecFuncDeclsWithSectionTo
        [ "foo @a @b @c (u :: a) (v :: b) (xs :: List c) :: List b"
            ++ "  = case xs of {"
            ++ "      Nil        -> Nil @b;"
            ++ "      Cons x xs' -> Cons @b v (foo @a @b @c u v xs')"
            ++ "    }"
        ]
        $ "Section section_foo. "
        ++ "(* Constant arguments for foo *) "
        ++ "Variable Shape : Type. "
        ++ "Variable Pos : Shape -> Type. "
        ++ "Variable b : Type. "
        ++ "Variable v : Free Shape Pos b. "
        ++ "(* Helper functions for foo *) "
        ++ "Fixpoint foo1 {a c : Type}"
        ++ "  (xs : List Shape Pos c) {struct xs}"
        ++ "  := match xs with"
        ++ "     | nil            => @Nil Shape Pos b"
        ++ "     | cons x xs' =>"
        ++ "        @Cons Shape Pos b v"
        ++ "          (xs' >>= (fun (xs'0 : List Shape Pos c) =>"
        ++ "                       foo1 xs'0))"
        ++ "     end. "
        ++ "(* Main functions for foo *) "
        ++ "Definition foo0 {a c : Type}"
        ++ "  (xs : Free Shape Pos (List Shape Pos c))"
        ++ "  : Free Shape Pos (List Shape Pos b)"
        ++ "  := xs >>= (fun (xs0 : List Shape Pos c) => foo1 xs0). "
        ++ "End section_foo. "
        ++ "Definition foo (Shape : Type) (Pos : Shape -> Type)"
        ++ "  {a b c : Type}"
        ++ "  (u : Free Shape Pos a)"
        ++ "  (v : Free Shape Pos b)"
        ++ "  (xs : Free Shape Pos (List Shape Pos c))"
        ++ "  : Free Shape Pos (List Shape Pos b)"
        ++ "  := foo0 Shape Pos b v xs."
