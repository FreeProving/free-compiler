-- | This module contains tests for "FreeC.Backend.Coq.Converter.FuncDecl.Rec".
module FreeC.Backend.Coq.Converter.FuncDecl.NonRecTests
  ( testConvertNonRecFuncDecl
  ) where

import           Test.Hspec

import           FreeC.Backend.Coq.Converter.FuncDecl.NonRec
import           FreeC.Backend.Coq.Pretty ()
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Test.Environment
import           FreeC.Test.Expectations
import           FreeC.Test.Parser

-------------------------------------------------------------------------------
-- Expectation Setters                                                       --
-------------------------------------------------------------------------------
-- | Parses the given IR function declaration, converts it to Coq using
--   'convertNonRecFuncDecl' and sets the expectation that the resulting
--   Coq code equals the given expected output modulo whitespace.
shouldConvertNonRecTo :: String -> String -> Converter Expectation
shouldConvertNonRecTo inputStr expectedOutputStr = do
  input <- parseTestFuncDecl inputStr
  output <- convertNonRecFuncDecl input
  return (output `prettyShouldBe` expectedOutputStr)

-------------------------------------------------------------------------------
-- Tests                                                                     --
-------------------------------------------------------------------------------
-- | Test group for 'convertNonRecFuncDecl' tests.
testConvertNonRecFuncDecl :: Spec
testConvertNonRecFuncDecl = context "non-recursive functions"
  $ do
    it "translates 0-ary functions correctly"
      $ shouldSucceedWith
      $ do
        "Integer" <- defineTestTypeCon "Integer" 0 []
        "foo" <- defineTestFunc "foo" 0 "Integer"
        shouldConvertNonRecTo "foo :: Integer = 42"
          $ "Definition foo (Shape : Type) (Pos : Shape -> Type)"
          ++ "  : Free Shape Pos (Integer Shape Pos)"
          ++ "  := pure 42%Z."
    it "translates polymorphic functions correctly"
      $ shouldSucceedWith
      $ do
        "foo" <- defineTestFunc "foo" 0 "forall a. a -> a"
        shouldConvertNonRecTo "foo @a (x :: a) :: a = x"
          $ "Definition foo (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (x : Free Shape Pos a) : Free Shape Pos a := x."
    it "uses type information from the AST not the environment"
      $ shouldSucceedWith
      $ do
        "foo" <- defineTestFunc "foo" 0 "forall b. b -> b"
        shouldConvertNonRecTo "foo @a (x :: a) :: a = x"
          $ "Definition foo (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (x : Free Shape Pos a) : Free Shape Pos a := x."
    it "translates functions with multiple arguments correctly"
      $ shouldSucceedWith
      $ do
        "Pair" <- defineTestTypeCon "Pair" 0 ["Pair"]
        (_, "Pair0") <- defineTestCon "Pair" 2 "forall a b. a -> b -> Pair a b"
        "foo" <- defineTestFunc "foo" 0 "forall a b. a -> b -> Pair a b"
        shouldConvertNonRecTo
          "foo @a @b (x :: a) (y :: b) :: Pair a b = Pair @a @b x y"
          $ "Definition foo (Shape : Type) (Pos : Shape -> Type) {a b : Type}"
          ++ "  (x : Free Shape Pos a) (y : Free Shape Pos b)"
          ++ "  : Free Shape Pos (Pair Shape Pos a b)"
          ++ "  := @Pair0 Shape Pos a b x y."
    it "translates higher order functions correctly"
      $ shouldSucceedWith
      $ do
        "Pair" <- defineTestTypeCon "Pair" 0 ["Pair"]
        (_, "Pair0") <- defineTestCon "Pair" 2 "forall a b. a -> b -> Pair a b"
        "curry" <- defineTestFunc "curry" 0
          "forall a b c. (Pair a b -> c) -> a -> b -> c"
        shouldConvertNonRecTo
          ("curry @a @b @c (f :: Pair a b -> c) (x :: a) (y :: b) :: c"
           ++ "  = f (Pair @a @b x y)")
          $ "Definition curry (Shape : Type) (Pos : Shape -> Type)"
          ++ "  {a b c : Type}"
          ++ "  (f : Free Shape Pos (Free Shape Pos (Pair Shape Pos a b)"
          ++ "    -> Free Shape Pos c))"
          ++ "  (x : Free Shape Pos a)"
          ++ "  (y : Free Shape Pos b)"
          ++ "  : Free Shape Pos c"
          ++ "  := f >>= (fun f_0 => f_0 (@Pair0 Shape Pos a b x y))."
    it "translates partial functions correctly"
      $ shouldSucceedWith
      $ do
        "List" <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
        ("nil", _) <- defineTestCon "Nil" 0 "forall a. List a"
        ("cons", _) <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
        "head" <- definePartialTestFunc "head" 1 "forall a. List a -> a"
        shouldConvertNonRecTo ("head @a (xs :: List a) :: a = case xs of {"
                               ++ "    Nil        -> undefined @a;"
                               ++ "    Cons x xs' -> x"
                               ++ "  }")
          $ "Definition head (Shape : Type) (Pos : Shape -> Type)"
          ++ "  (P : Partial Shape Pos) {a : Type}"
          ++ "  (xs : Free Shape Pos (List Shape Pos a))"
          ++ "  : Free Shape Pos a"
          ++ "  := xs >>= (fun xs_0 =>"
          ++ "       match xs_0 with"
          ++ "       | nil        => @undefined Shape Pos P a"
          ++ "       | cons x xs' => x"
          ++ "       end)."
    it "uses partiality information from the environment"
      $ shouldSucceedWith
      $ do
        "List" <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
        ("nil", _) <- defineTestCon "Nil" 0 "forall a. List a"
        ("cons", _) <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
        "head" <- defineTestFunc "head" 1 "forall a. List a -> a"
        -- Note the missing binding for the Partial type class instance below.
        -- `head` is not marked as partial in the environment. `undefined`
        -- still expects `P` to be an instance of `Partial`.
        shouldConvertNonRecTo ("head @a (xs :: List a) :: a = case xs of {"
                               ++ "    Nil        -> undefined @a;"
                               ++ "    Cons x xs' -> x"
                               ++ "  }")
          $ "Definition head (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (xs : Free Shape Pos (List Shape Pos a))"
          ++ "  : Free Shape Pos a"
          ++ "  := xs >>= (fun xs_0 =>"
          ++ "       match xs_0 with"
          ++ "       | nil        => @undefined Shape Pos P a"
          ++ "       | cons x xs' => x"
          ++ "       end)."
    it "allows the function arguments to be shadowed"
      $ shouldSucceedWith
      $ do
        "List" <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
        ("nil", _) <- defineTestCon "Nil" 0 "forall a. List a"
        ("cons", _) <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
        "tail" <- definePartialTestFunc "tail" 1 "forall a. List a -> List a"
        shouldConvertNonRecTo ("tail @a (xs :: List a) :: List a = case xs of {"
                               ++ "    Nil       -> undefined @(List a);"
                               ++ "    Cons x xs -> xs"
                               ++ "}")
          $ "Definition tail (Shape : Type) (Pos : Shape -> Type)"
          ++ "  (P : Partial Shape Pos) {a : Type}"
          ++ "  (xs : Free Shape Pos (List Shape Pos a))"
          ++ "  : Free Shape Pos (List Shape Pos a)"
          ++ " := xs >>= (fun xs_0 =>"
          ++ "    match xs_0 with"
          ++ "    | nil       => @undefined Shape Pos P (List Shape Pos a)"
          ++ "    | cons x xs0 => xs0"
          ++ "    end)."
    it "translates functions with one strict argument correctly"
      $ shouldSucceedWith
      $ do
        "List" <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
        ("nil", _) <- defineTestCon "Nil" 0 "forall a. List a"
        ("cons", _) <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
        "head"
          <- definePartialStrictTestFunc "head" [True] "forall a. List a -> a"
        shouldConvertNonRecTo
          ("head @a !(x :: List a) :: a = case x of {"
           ++ "    Cons h xs -> h;"
           ++ "    Nil       -> error @a \"head was called on an empty list\""
           ++ "}")
          $ "Definition head (Shape : Type) (Pos : Shape -> Type)"
          ++ "  (P : Partial Shape Pos) {a : Type}"
          ++ "  (x : List Shape Pos a)"
          ++ "  : Free Shape Pos a"
          ++ " := match x with"
          ++ "    | cons h xs => h"
          ++ "    | nil       => @error Shape Pos P a"
          ++ "                     \"head was called on an empty list\"%string"
          ++ "    end."
    it "translates functions with strict and non-strict arguments correctly"
      $ shouldSucceedWith
      $ do
        "List" <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
        ("nil", _) <- defineTestCon "Nil" 0 "forall a. List a"
        ("cons", _) <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
        "Pair" <- defineTestTypeCon "Pair" 2 ["Pair0"]
        ("pair0", _) <- defineTestCon "Pair0" 2 "forall a b. a -> b -> Pair a b"
        "Bool" <- defineTestTypeCon "Bool" 0 ["False", "True"]
        ("false", _) <- defineTestCon "False" 0 "Bool"
        ("true", _) <- defineTestCon "True" 0 "Bool"
        "foo" <- defineStrictTestFunc "foo" [True, False, True]
          "forall a. Pair a a -> Bool -> List a -> List a"
        shouldConvertNonRecTo
          ("foo @a !(pair :: Pair a a) (bool :: Bool) !(list :: List a)"
           ++ "  :: List a ="
           ++ "  case pair of {"
           ++ "    Pair0 p1 p2 ->"
           ++ "      case list of {"
           ++ "        Nil ->"
           ++ "          case bool of {"
           ++ "            True  -> Cons @a p1 (Nil @a);"
           ++ "            False -> Cons @a p2 (Nil @a)"
           ++ "          };"
           ++ "        Cons x xs ->"
           ++ "          case bool of {"
           ++ "            True  -> Cons @a p1 xs;"
           ++ "            False -> Cons @a p2 xs"
           ++ "          }"
           ++ "      }"
           ++ "  }")
          $ "Definition foo (Shape : Type) (Pos : Shape -> Type)"
          ++ "  {a : Type} (pair : Pair Shape Pos a a)"
          ++ "  (bool : Free Shape Pos (Bool Shape Pos))"
          ++ "  (list : List Shape Pos a)"
          ++ "  : Free Shape Pos (List Shape Pos a)"
          ++ " := let 'pair0 p1 p2 := pair"
          ++ "    in match list with"
          ++ "       | nil =>"
          ++ "           bool >>= (fun bool_0 =>"
          ++ "             match bool_0 with"
          ++ "             | true  => @Cons Shape Pos a p1 (@Nil Shape Pos a)"
          ++ "             | false => @Cons Shape Pos a p2 (@Nil Shape Pos a)"
          ++ "             end)"
          ++ "       | cons x xs =>"
          ++ "           bool >>= (fun bool_0 =>"
          ++ "             match bool_0 with"
          ++ "             | true  => @Cons Shape Pos a p1 xs"
          ++ "             | false => @Cons Shape Pos a p2 xs"
          ++ "             end)"
          ++ "       end."
    it "translates case expressions with one strict pattern correctly"
      $ shouldSucceedWith
      $ do
        "List" <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
        ("nil", _) <- defineTestCon "Nil" 0 "forall a. List a"
        ("cons", _) <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
        "head" <- definePartialTestFunc "head" 1 "forall a. List a -> a"
        shouldConvertNonRecTo
          ("head @a (x :: List a) :: a = case x of {"
           ++ "    Cons !h xs -> h;"
           ++ "    Nil        -> error @a \"head was called on a empty list\""
           ++ "}")
          $ "Definition head (Shape : Type) (Pos : Shape -> Type)"
          ++ "  (P : Partial Shape Pos) {a : Type}"
          ++ "  (x : Free Shape Pos (List Shape Pos a))"
          ++ "  : Free Shape Pos a"
          ++ " := x >>= (fun x_0 =>"
          ++ "    match x_0 with"
          ++ "    | cons h_0 xs => h_0 >>= (fun h => pure h)"
          ++ "    | nil => @error Shape Pos P a"
          ++ "               \"head was called on a empty list\"%string"
          ++ "    end)."
    it ("translates case expressions with strict and non-strict patterns "
        ++ "correctly")
      $ shouldSucceedWith
      $ do
        "Triple" <- defineTestTypeCon "Triple" 3 ["Triple0"]
        ("triple0", _) <- defineTestCon "Triple0" 3
          "forall a b c. a -> b -> c -> Triple a b c"
        "Int" <- defineTestTypeCon "Int" 0 []
        "succ" <- defineTestFunc "succ" 1 "Int -> Int"
        "succTriple" <- defineTestFunc "succTriple" 1
          "Triple Int Int Int -> Triple Int Int Int"
        shouldConvertNonRecTo
          ("succTriple (triple :: Triple Int Int Int)"
           ++ " :: Triple Int Int Int = case triple of {"
           ++ "    Triple0 i1 !i2 !i3 ->"
           ++ "      Triple0 @Int @Int @Int (succ i1) (succ i2) (succ i3)"
           ++ "    }")
          $ "Definition succTriple (Shape : Type) (Pos : Shape -> Type)"
          ++ "  (triple : Free Shape Pos (Triple Shape Pos (Int Shape Pos)"
          ++ "                                             (Int Shape Pos)"
          ++ "                                             (Int Shape Pos)))"
          ++ "  : Free Shape Pos (Triple Shape Pos (Int Shape Pos)"
          ++ "                                     (Int Shape Pos)"
          ++ "                                     (Int Shape Pos))"
          ++ " := triple >>= (fun '(triple0 i1 i2_0 i3_0) =>"
          ++ "      i2_0 >>= (fun i2 => i3_0 >>= (fun i3 =>"
          ++ "        @Triple0 Shape Pos"
          ++ "                 (Int Shape Pos) (Int Shape Pos) (Int Shape Pos)"
          ++ "                 (succ Shape Pos i1)"
          ++ "                 (succ Shape Pos (pure i2))"
          ++ "                 (succ Shape Pos (pure i3)))))."
