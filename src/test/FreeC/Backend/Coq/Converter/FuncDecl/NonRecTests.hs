-- | This module contains tests for "FreeC.Backend.Coq.Converter.FuncDecl.Rec".

module FreeC.Backend.Coq.Converter.FuncDecl.NonRecTests
  ( testConvertNonRecFuncDecl
  )
where

import           Test.Hspec

import           FreeC.Backend.Coq.Converter.FuncDecl.NonRec
import           FreeC.Backend.Coq.Pretty       ( )
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Test.Environment
import           FreeC.Test.Expectations
import           FreeC.Test.Parser

-------------------------------------------------------------------------------
-- Expectation setters                                                       --
-------------------------------------------------------------------------------

-- | Parses the given IR function declaration, converts it to Coq using
--   'convertNonRecFuncDecl' and sets the expectation that the resulting
--   Coq code equals the given expected output modulo white space.
shouldConvertNonRecTo :: String -> String -> Converter Expectation
shouldConvertNonRecTo inputStr expectedOutputStr = do
  input  <- parseTestFuncDecl inputStr
  output <- convertNonRecFuncDecl input
  return (output `prettyShouldBe` expectedOutputStr)

-------------------------------------------------------------------------------
-- Tests                                                                     --
-------------------------------------------------------------------------------

-- | Test group for 'convertNonRecFuncDecl' tests.
testConvertNonRecFuncDecl :: Spec
testConvertNonRecFuncDecl = context "non-recursive functions" $ do
  it "translates 0-ary functions correctly" $ shouldSucceedWith $ do
    "Integer" <- defineTestTypeCon "Integer" 0 []
    "foo"     <- defineTestFunc "foo" 0 "Integer"
    shouldConvertNonRecTo "foo :: Integer = 42"
      $  "Definition foo (Shape : Type) (Pos : Shape -> Type)"
      ++ "  : Free Shape Pos (Integer Shape Pos)"
      ++ "  := pure 42%Z."

  it "translates polymorphic functions correctly" $ shouldSucceedWith $ do
    "foo" <- defineTestFunc "foo" 0 "forall a. a -> a"
    shouldConvertNonRecTo "foo @a (x :: a) :: a = x"
      $  "Definition foo (Shape : Type) (Pos : Shape -> Type) {a : Type}"
      ++ "  (x : Free Shape Pos a) : Free Shape Pos a := x."

  it "uses type information from the AST not the environment"
    $ shouldSucceedWith
    $ do
        "foo" <- defineTestFunc "foo" 0 "forall b. b -> b"
        shouldConvertNonRecTo "foo @a (x :: a) :: a = x"
          $  "Definition foo (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (x : Free Shape Pos a) : Free Shape Pos a := x."

  it "translates functions with multiple arguments correctly"
    $ shouldSucceedWith
    $ do
        "Pair"       <- defineTestTypeCon "Pair" 0 ["Pair"]
        (_, "Pair0") <- defineTestCon "Pair" 2 "forall a b. a -> b -> Pair a b"
        "foo"        <- defineTestFunc "foo" 0 "forall a b. a -> b -> Pair a b"
        shouldConvertNonRecTo
            "foo @a @b (x :: a) (y :: b) :: Pair a b = Pair @a @b x y"
          $  "Definition foo (Shape : Type) (Pos : Shape -> Type) {a b : Type}"
          ++ "  (x : Free Shape Pos a) (y : Free Shape Pos b)"
          ++ "  : Free Shape Pos (Pair Shape Pos a b)"
          ++ "  := @Pair0 Shape Pos a b x y."

  it "translates higher order functions correctly" $ shouldSucceedWith $ do
    "Pair" <- defineTestTypeCon "Pair" 0 ["Pair"]
    (_, "Pair0") <- defineTestCon "Pair" 2 "forall a b. a -> b -> Pair a b"
    "curry" <- defineTestFunc "curry"
                              0
                              "forall a b c. (Pair a b -> c) -> a -> b -> c"
    shouldConvertNonRecTo
        (  "curry @a @b @c (f :: Pair a b -> c) (x :: a) (y :: b) :: c"
        ++ "  = f (Pair @a @b x y)"
        )
      $  "Definition curry (Shape : Type) (Pos : Shape -> Type)"
      ++ "  {a b c : Type}"
      ++ "  (f : Free Shape Pos (Free Shape Pos (Pair Shape Pos a b)"
      ++ "    -> Free Shape Pos c))"
      ++ "  (x : Free Shape Pos a)"
      ++ "  (y : Free Shape Pos b)"
      ++ "  : Free Shape Pos c"
      ++ "  := f >>= (fun f_0 => f_0 (@Pair0 Shape Pos a b x y))."

  it "translates partial functions correctly" $ shouldSucceedWith $ do
    "List"      <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
    ("nil" , _) <- defineTestCon "Nil" 0 "forall a. List a"
    ("cons", _) <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
    "head"      <- definePartialTestFunc "head" 1 "forall a. List a -> a"
    shouldConvertNonRecTo
        (  "head @a (xs :: List a) :: a = case xs of {"
        ++ "    Nil        -> undefined @a;"
        ++ "    Cons x xs' -> x"
        ++ "  }"
        )
      $  "Definition head (Shape : Type) (Pos : Shape -> Type)"
      ++ "  (P : Partial Shape Pos) {a : Type}"
      ++ "  (xs : Free Shape Pos (List Shape Pos a))"
      ++ "  : Free Shape Pos a"
      ++ "  := xs >>= (fun xs_0 =>"
      ++ "       match xs_0 with"
      ++ "       | nil        => @undefined Shape Pos P a"
      ++ "       | cons x xs' => x"
      ++ "       end)."

  it "uses partiality information from the environment" $ shouldSucceedWith $ do
    "List"      <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
    ("nil" , _) <- defineTestCon "Nil" 0 "forall a. List a"
    ("cons", _) <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
    "head"      <- defineTestFunc "head" 1 "forall a. List a -> a"
    shouldConvertNonRecTo
        (  "head @a (xs :: List a) :: a = case xs of {"
        ++ "    Nil        -> undefined @a;"
        ++ "    Cons x xs' -> x"
        ++ "  }"
        )
         -- Note the missing binding for the Partial type class instance below.
         -- `head` is not marked as partial in the environment. `undefined`
         -- still expects `P` to be an instance of `Partial`.
      $  "Definition head (Shape : Type) (Pos : Shape -> Type) {a : Type}"
      ++ "  (xs : Free Shape Pos (List Shape Pos a))"
      ++ "  : Free Shape Pos a"
      ++ "  := xs >>= (fun xs_0 =>"
      ++ "       match xs_0 with"
      ++ "       | nil        => @undefined Shape Pos P a"
      ++ "       | cons x xs' => x"
      ++ "       end)."

  it "allows the function arguments to be shadowed" $ shouldSucceedWith $ do
    "List"      <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
    ("nil" , _) <- defineTestCon "Nil" 0 "forall a. List a"
    ("cons", _) <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
    "tail"      <- definePartialTestFunc "tail" 1 "forall a. List a -> List a"
    shouldConvertNonRecTo
        (  "tail @a (xs :: List a) :: List a = case xs of {"
        ++ "    Nil       -> undefined @(List a);"
        ++ "    Cons x xs -> xs"
        ++ "}"
        )
      $  "Definition tail (Shape : Type) (Pos : Shape -> Type)"
      ++ "  (P : Partial Shape Pos) {a : Type}"
      ++ "  (xs : Free Shape Pos (List Shape Pos a))"
      ++ "  : Free Shape Pos (List Shape Pos a)"
      ++ " := xs >>= (fun xs_0 =>"
      ++ "    match xs_0 with"
      ++ "    | nil       => @undefined Shape Pos P (List Shape Pos a)"
      ++ "    | cons x xs0 => xs0"
      ++ "    end)."
