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
      $ "Section section_map_0. "
      ++ "(* Constant arguments for map *) "
      ++ "Variable Shape : Type. "
      ++ "Variable Pos : Shape -> Type. "
      ++ "Variable a_0 b_0 : Type. "
      ++ "Variable f_0 : Free Shape Pos"
      ++ "  (Free Shape Pos a_0 -> Free Shape Pos b_0). "
      ++ "(* Helper functions for map *) "
      ++ "Fixpoint map_1 (xs : List Shape Pos a_0) {struct xs}"
      ++ "  := match xs with"
      ++ "     | nil            => @Nil Shape Pos b_0"
      ++ "     | cons x xs' =>"
      ++ "        @Cons Shape Pos b_0"
      ++ "          (f_0 >>= (fun f_1 => f_1 x))"
      ++ "          (xs' >>= (fun (xs'_0 : List Shape Pos a_0) =>"
      ++ "             map_1 xs'_0))"
      ++ "     end. "
      ++ "(* Main functions for map *) "
      ++ "Definition map_0 (xs : Free Shape Pos (List Shape Pos a_0))"
      ++ "  : Free Shape Pos (List Shape Pos b_0)"
      ++ "  := xs >>= (fun (xs_0 : List Shape Pos a_0) => map_1 xs_0). "
      ++ "End section_map_0. "
      ++ "Definition map (Shape : Type) (Pos : Shape -> Type)"
      ++ "  {a b : Type}"
      ++ "  (f : Free Shape Pos (Free Shape Pos a -> Free Shape Pos b))"
      ++ "  (xs : Free Shape Pos (List Shape Pos a))"
      ++ "  : Free Shape Pos (List Shape Pos b)"
      ++ "  := map_0 Shape Pos a b f xs."
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
        $ "Section section_mapAlt_mapAlt'_0. "
        ++ "(* Constant arguments for mapAlt, mapAlt' *) "
        ++ "Variable Shape : Type. "
        ++ "Variable Pos : Shape -> Type. "
        ++ "Variable a_0 b_0 : Type. "
        ++ "Variable f_0 : Free Shape Pos"
        ++ "  (Free Shape Pos a_0 -> Free Shape Pos b_0). "
        ++ "(* Helper functions for mapAlt, mapAlt' *) "
        ++ "Fixpoint mapAlt_1 (xs : List Shape Pos a_0) {struct xs}"
        ++ "  := match xs with"
        ++ "     | nil            => @Nil Shape Pos b_0"
        ++ "     | cons x xs' =>"
        ++ "        @Cons Shape Pos b_0"
        ++ "          (f_0 >>= (fun f_1 => f_1 x))"
        ++ "          (xs' >>= (fun (xs'_0 : List Shape Pos a_0) =>"
        ++ "             mapAlt'_1 xs'_0))"
        ++ "     end"
        ++ " with mapAlt'_1 (xs : List Shape Pos a_0) {struct xs}"
        ++ "  := match xs with"
        ++ "     | nil            => @Nil Shape Pos b_0"
        ++ "     | cons x xs' =>"
        ++ "        @Cons Shape Pos b_0"
        ++ "          (f_0 >>= (fun f_1 => f_1 x))"
        ++ "          (xs' >>= (fun (xs'_0 : List Shape Pos a_0) =>"
        ++ "             mapAlt_1 xs'_0))"
        ++ "     end. "
        ++ "(* Main functions for mapAlt, mapAlt' *) "
        ++ "Definition mapAlt_0 (xs : Free Shape Pos (List Shape Pos a_0))"
        ++ "  : Free Shape Pos (List Shape Pos b_0)"
        ++ "  := xs >>= (fun (xs_0 : List Shape Pos a_0) => mapAlt_1 xs_0). "
        ++ "Definition mapAlt'_0 (xs : Free Shape Pos (List Shape Pos a_0))"
        ++ "  : Free Shape Pos (List Shape Pos b_0)"
        ++ "  := xs >>= (fun (xs_0 : List Shape Pos a_0) => mapAlt'_1 xs_0). "
        ++ "End section_mapAlt_mapAlt'_0. "
        ++ "Definition mapAlt (Shape : Type) (Pos : Shape -> Type)"
        ++ "  {a b : Type}"
        ++ "  (f : Free Shape Pos (Free Shape Pos a -> Free Shape Pos b))"
        ++ "  (xs : Free Shape Pos (List Shape Pos a))"
        ++ "  : Free Shape Pos (List Shape Pos b)"
        ++ "  := mapAlt_0 Shape Pos a b f xs. "
        ++ "Definition mapAlt' (Shape : Type) (Pos : Shape -> Type)"
        ++ "  {b a : Type}"
        ++ "  (f : Free Shape Pos (Free Shape Pos b -> Free Shape Pos a))"
        ++ "  (xs : Free Shape Pos (List Shape Pos b))"
        ++ "  : Free Shape Pos (List Shape Pos a)"
        ++ "  := mapAlt'_0 Shape Pos b a f xs."
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
        $ "Section section_foo_0. "
        ++ "(* Constant arguments for foo *) "
        ++ "Variable Shape : Type. "
        ++ "Variable Pos : Shape -> Type. "
        ++ "Variable a_0 : Type. "
        ++ "Variable v_0 : Free Shape Pos a_0. "
        ++ "(* Helper functions for foo *) "
        ++ "Fixpoint foo_1 (xs : List Shape Pos a_0) {struct xs}"
        ++ "  := match xs with"
        ++ "     | nil            => @Nil Shape Pos a_0"
        ++ "     | cons x xs' =>"
        ++ "        @Cons Shape Pos a_0 v_0"
        ++ "          (xs' >>= (fun (xs'_0 : List Shape Pos a_0) =>"
        ++ "              foo_1 xs'_0))"
        ++ "     end. "
        ++ "(* Main functions for foo *) "
        ++ "Definition foo_0 (xs : Free Shape Pos (List Shape Pos a_0))"
        ++ "  : Free Shape Pos (List Shape Pos a_0)"
        ++ "  := xs >>= (fun (xs_0 : List Shape Pos a_0) => foo_1 xs_0). "
        ++ "End section_foo_0. "
        ++ "Definition foo (Shape : Type) (Pos : Shape -> Type)"
        ++ "  {a : Type}"
        ++ "  (u : Free Shape Pos a)"
        ++ "  (v : Free Shape Pos a)"
        ++ "  (xs : Free Shape Pos (List Shape Pos a))"
        ++ "  : Free Shape Pos (List Shape Pos a)"
        ++ "  := foo_0 Shape Pos a v xs."
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
        $ "Section section_foo_0. "
        ++ "(* Constant arguments for foo *) "
        ++ "Variable Shape : Type. "
        ++ "Variable Pos : Shape -> Type. "
        ++ "Variable b_0 : Type. "
        ++ "Variable v_0 : Free Shape Pos b_0. "
        ++ "(* Helper functions for foo *) "
        ++ "Fixpoint foo_1 {a_0 c_0 : Type}"
        ++ "  (xs : List Shape Pos c_0) {struct xs}"
        ++ "  := match xs with"
        ++ "     | nil            => @Nil Shape Pos b_0"
        ++ "     | cons x xs' =>"
        ++ "        @Cons Shape Pos b_0 v_0"
        ++ "          (xs' >>= (fun (xs'_0 : List Shape Pos c_0) =>"
        ++ "                       foo_1 xs'_0))"
        ++ "     end. "
        ++ "(* Main functions for foo *) "
        ++ "Definition foo_0 {a_0 c_0 : Type}"
        ++ "  (xs : Free Shape Pos (List Shape Pos c_0))"
        ++ "  : Free Shape Pos (List Shape Pos b_0)"
        ++ "  := xs >>= (fun (xs_0 : List Shape Pos c_0) => foo_1 xs_0). "
        ++ "End section_foo_0. "
        ++ "Definition foo (Shape : Type) (Pos : Shape -> Type)"
        ++ "  {a b c : Type}"
        ++ "  (u : Free Shape Pos a)"
        ++ "  (v : Free Shape Pos b)"
        ++ "  (xs : Free Shape Pos (List Shape Pos c))"
        ++ "  : Free Shape Pos (List Shape Pos b)"
        ++ "  := foo_0 Shape Pos b v xs."
