-- | This module contains tests for
--   "FreeC.Backend.Coq.Converter.FuncDecl.Rec.WithHelpers".

module FreeC.Backend.Coq.Converter.FuncDecl.Rec.WithHelpersTests
  ( testConvertRecFuncDeclWithHelpers
  )
where

import           Test.Hspec

import           FreeC.Backend.Coq.Converter.FuncDecl.Rec.WithHelpers
import           FreeC.Backend.Coq.Pretty       ( )
import           FreeC.Environment              ( emptyEnv )
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter           ( runReporter )
import           FreeC.Test.Environment
import           FreeC.Test.Expectations
import           FreeC.Test.Parser


-------------------------------------------------------------------------------
-- Expectation setters                                                       --
-------------------------------------------------------------------------------

-- | Parses the given function declarations, converts them to Coq using
--   'convertRecFuncDeclsWithHelpers' and expects the resulting Coq code
--   to equal the given expected output modulo white space.
shouldConvertWithHelpersTo :: [String] -> String -> Converter Expectation
shouldConvertWithHelpersTo inputStrs expectedOutputStr = do
  input  <- mapM parseTestFuncDecl inputStrs
  output <- convertRecFuncDeclsWithHelpers input
  return (output `prettyShouldBe` expectedOutputStr)

-- | Runs a converter and uses the resulting environment and messages to
--   produce an empty string to be printed before forwarding the result.
avoidLaziness :: Converter a -> IO a
avoidLaziness c =
  let (mbResEnv, msgs) = runReporter $ runConverter c emptyEnv
      (res     , str ) = case mbResEnv of
        Nothing          -> error "no result"
        Just (res', env) -> (res', show env ++ show msgs)
  in  do
        putStr $ drop (length str) str
        return res

-------------------------------------------------------------------------------
-- Tests                                                                     --
-------------------------------------------------------------------------------

-- | Test group for 'convertRecFuncDeclsWithHelpers' tests.
testConvertRecFuncDeclWithHelpers :: Spec
testConvertRecFuncDeclWithHelpers = context "with helper functions" $ do
  it "requires an argument" $ do
    input <- expectParseTestFuncDecl "loop @a :: a = loop @a"
    shouldFail $ do
      "loop" <- defineTestFunc "loop" 0 "forall a. a"
      convertRecFuncDeclsWithHelpers [input]

  it "requires a case expression (if expressions don't suffice)" $ do
    input <- expectParseTestFuncDecl
      (  "fac (n :: Integer) :: Integer"
      ++ "  = if (==) n 0 then 1 else (*) n (fac (pred n))"
      )
    shouldFail $ do
      _ <- defineTestTypeCon "Integer" 0
      _ <- defineTestFunc "fac" 1 "Integer -> Integer"
      _ <- defineTestFunc "pred" 1 "Integer -> Integer"
      _ <- defineTestFunc "(*)" 1 "Integer -> Integer -> Integer"
      _ <- defineTestFunc "(==)" 1 "Integer -> Integer -> Bool"
      convertRecFuncDeclsWithHelpers [input]

  it "requires the case expression to match an argument" $ do
    input <- expectParseTestFuncDecl
      "loop @a :: a = case f of { () -> loop @a }"
    shouldFail $ do
      _ <- defineTestTypeCon "()" 0
      _ <- defineTestCon "()" 0 "()"
      _ <- defineTestFunc "f" 0 "()"
      _ <- defineTestFunc "loop" 0 "forall a. a"
      convertRecFuncDeclsWithHelpers [input]

  it "requires a decreasing argument" $ do
    input <- expectParseTestFuncDecl
      "loop @a (x :: a) :: a = case x of { () -> loop @a x }"
    shouldFail $ do
      _ <- defineTestFunc "loop" 0 "forall a. a -> a"
      convertRecFuncDeclsWithHelpers [input]

  it "translates simple recursive functions correctly" $ shouldSucceedWith $ do
    "Integer"        <- defineTestTypeCon "Integer" 0
    "succ"           <- defineTestFunc "succ" 1 "Integer -> Integer"
    "List"           <- defineTestTypeCon "List" 1
    ("nil" , "Nil" ) <- defineTestCon "Nil" 0 "forall a. List a"
    ("cons", "Cons") <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
    "length"         <- defineTestFunc "length" 1 "forall a. List a -> Integer"
    shouldConvertWithHelpersTo
        [ "length @a (xs :: List a) :: Integer = case xs of {"
          ++ "    Nil        -> 0;"
          ++ "    Cons x xs' -> succ (length @a xs')"
          ++ "  }"
        ]
      $  "(* Helper functions for length *) "
      ++ "Fixpoint length_0 (Shape : Type) (Pos : Shape -> Type) {a : Type}"
      ++ "  (xs : List Shape Pos a)"
      ++ "  {struct xs}"
      ++ "  := match xs with"
      ++ "     | nil        => pure 0%Z"
      ++ "     | cons x xs' => succ Shape Pos"
      ++ "         (xs' >>= (fun (xs'_0 : List Shape Pos a) =>"
      ++ "           @length_0 Shape Pos a xs'_0))"
      ++ "     end. "
      ++ "Definition length (Shape : Type) (Pos : Shape -> Type) {a : Type}"
      ++ "  (xs : Free Shape Pos (List Shape Pos a))"
      ++ "  : Free Shape Pos (Integer Shape Pos)"
      ++ "  := xs >>= (fun (xs_0 : List Shape Pos a) =>"
      ++ "       @length_0 Shape Pos a xs_0)."

  it "uses expression type annotations for return type of helper functions"
    $ shouldSucceedWith
    $ do
        "Integer"        <- defineTestTypeCon "Integer" 0
        "succ"           <- defineTestFunc "succ" 1 "Integer -> Integer"
        "List"           <- defineTestTypeCon "List" 1
        ("nil" , "Nil" ) <- defineTestCon "Nil" 0 "forall a. List a"
        ("cons", "Cons") <- defineTestCon "Cons"
                                          2
                                          "forall a. a -> List a -> List a"
        "length" <- defineTestFunc "length" 1 "forall a. List a -> Integer"
        shouldConvertWithHelpersTo
            [ "length @a (xs :: List a) :: Integer = case xs of {"
              ++ "    Nil        -> 0;"
              ++ "    Cons x xs' -> succ (length @a xs')"
              ++ "  } :: Integer"
            ]
          $  "(* Helper functions for length *) "
          ++ "Fixpoint length_0 (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (xs : List Shape Pos a)"
          ++ "  {struct xs}"
          ++ " : Free Shape Pos (Integer Shape Pos)" -- <-- Helper return type.
          ++ "  := match xs with"
          ++ "     | nil        => pure 0%Z"
          ++ "     | cons x xs' => succ Shape Pos"
          ++ "         (xs' >>= (fun (xs'_0 : List Shape Pos a) =>"
          ++ "           @length_0 Shape Pos a xs'_0))"
          ++ "     end. "
          ++ "Definition length (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (xs : Free Shape Pos (List Shape Pos a))"
          ++ "  : Free Shape Pos (Integer Shape Pos)"
          ++ "  := xs >>= (fun (xs_0 : List Shape Pos a) =>"
          ++ "       @length_0 Shape Pos a xs_0)."

  it "translates partial recursive functions correctly" $ shouldSucceedWith $ do
    "Bool"           <- defineTestTypeCon "Prelude.Bool" 0
    "List"           <- defineTestTypeCon "List" 1
    ("nil" , "Nil" ) <- defineTestCon "Nil" 0 "forall a. List a"
    ("cons", "Cons") <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
    "findJust" <- definePartialTestFunc "findJust"
                                        2
                                        "forall a. (a -> Bool) -> List a -> a"
    shouldConvertWithHelpersTo
        [ "findJust @a (p :: a -> Prelude.Bool) (xs :: List a) :: a"
          ++ "  = case xs of {"
          ++ "      Nil        -> undefined @a;"
          ++ "      Cons x xs' -> if p x then x else findJust @a p xs'"
          ++ "    }"
        ]
      $  "(* Helper functions for findJust *) "
      ++ "Fixpoint findJust_0 (Shape : Type) (Pos : Shape -> Type)"
      ++ "  (P : Partial Shape Pos) {a : Type}"
      ++ "  (p : Free Shape Pos (Free Shape Pos a"
      ++ "    -> Free Shape Pos (Bool Shape Pos)))"
      ++ "  (xs : List Shape Pos a) {struct xs}"
      ++ "  := match xs with"
      ++ "     | nil            => @undefined Shape Pos P a"
      ++ "     | cons x xs' =>"
      ++ "        (p >>= (fun p_1 => p_1 x)) >>="
      ++ "        (fun (cond_0 : Bool Shape Pos) =>"
      ++ "           if cond_0"
      ++ "           then x"
      ++ "           else xs' >>= (fun (xs'_0 : List Shape Pos a) =>"
      ++ "                           @findJust_0 Shape Pos P a p xs'_0))"
      ++ "     end. "
      ++ "Definition findJust (Shape : Type) (Pos : Shape -> Type)"
      ++ "  (P : Partial Shape Pos) {a : Type}"
      ++ "  (p : Free Shape Pos (Free Shape Pos a"
      ++ "    -> Free Shape Pos (Bool Shape Pos)))"
      ++ "  (xs : Free Shape Pos (List Shape Pos a))"
      ++ "  : Free Shape Pos a"
      ++ "  := xs >>= (fun (xs_0 : List Shape Pos a) =>"
      ++ "               @findJust_0 Shape Pos P a p xs_0)."

  it "translates mutually recursive functions correctly"
    $ shouldSucceedWith
    $ do
        "Bool"           <- defineTestTypeCon "Bool" 0
        (_, "True" )     <- defineTestCon "True" 0 "Bool"
        (_, "False")     <- defineTestCon "False" 0 "Bool"
        "List"           <- defineTestTypeCon "List" 1
        ("nil" , "Nil" ) <- defineTestCon "Nil" 0 "forall a. List a"
        ("cons", "Cons") <- defineTestCon "Cons"
                                          2
                                          "forall a. a -> List a -> List a"
        "even_len" <- defineTestFunc "even_len" 1 "forall a. List a -> Bool"
        "odd_len"  <- defineTestFunc "odd_len" 1 "forall a. List a -> Bool"
        shouldConvertWithHelpersTo
            [ "even_len @a (xs :: List a) :: Bool = case xs of {"
            ++ "    Nil -> True;"
            ++ "    Cons x xs' -> odd_len @a xs'"
            ++ "  }"
            , "odd_len @a (xs :: List a) :: Bool = case xs of {"
            ++ "    Nil -> False;"
            ++ "    Cons x xs' -> even_len @a xs'"
            ++ "  }"
            ]
          $  "(* Helper functions for even_len, odd_len *) "
          ++ "Fixpoint even_len_0 (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (xs : List Shape Pos a)"
          ++ "  {struct xs}"
          ++ "  := match xs with"
          ++ "     | nil        => True Shape Pos"
          ++ "     | cons x xs' =>"
          ++ "         xs' >>= (fun (xs'_0 : List Shape Pos a) =>"
          ++ "           @odd_len_0 Shape Pos a xs'_0)"
          ++ "     end "
          ++ "with odd_len_0 (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (xs : List Shape Pos a)"
          ++ "  {struct xs}"
          ++ "  := match xs with"
          ++ "     | nil        => False Shape Pos"
          ++ "     | cons x xs' =>"
          ++ "         xs' >>= (fun (xs'_0 : List Shape Pos a) =>"
          ++ "           @even_len_0 Shape Pos a xs'_0)"
          ++ "     end. "
          ++ "Definition even_len (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (xs : Free Shape Pos (List Shape Pos a))"
          ++ "  : Free Shape Pos (Bool Shape Pos)"
          ++ "  := xs >>= (fun (xs_0 : List Shape Pos a) =>"
          ++ "           @even_len_0 Shape Pos a xs_0). "
          ++ "Definition odd_len (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (xs : Free Shape Pos (List Shape Pos a))"
          ++ "  : Free Shape Pos (Bool Shape Pos)"
          ++ "  := xs >>= (fun (xs_0 : List Shape Pos a) =>"
          ++ "           @odd_len_0 Shape Pos a xs_0)."


  it "translates recursive functions with nested case expressions correctly"
    $ shouldSucceedWith
    $ do
        "List"           <- defineTestTypeCon "List" 1
        ("nil" , "Nil" ) <- defineTestCon "Nil" 0 "forall a. List a"
        ("cons", "Cons") <- defineTestCon "Cons"
                                          2
                                          "forall a. a -> List a -> List a"
        "tails" <- defineTestFunc "tails"
                                  1
                                  "forall a. List a -> (List (List a))"
        shouldConvertWithHelpersTo
            [ "tails @a (xs :: List a) :: List (List a)"
              ++ "  = Cons @(List a) xs (case xs of {"
              ++ "                         Nil        -> Nil @(List a);"
              ++ "                         Cons x xs' -> tails @a xs'"
              ++ "                       })"
            ]
          $  "(* Helper functions for tails *) "
          ++ "Fixpoint tails_0 (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (xs : List Shape Pos a)"
          ++ "  {struct xs}"
          ++ "  := match xs with"
          ++ "     | nil => @Nil Shape Pos (List Shape Pos a)"
          ++ "     | cons x xs' => @Cons Shape Pos (List Shape Pos a) xs'"
          ++ "         (xs' >>=  (fun (xs'_0 : List Shape Pos a) =>"
          ++ "            @tails_0 Shape Pos a xs'_0))"
          ++ "     end. "
          ++ " Definition tails (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "   (xs : Free Shape Pos (List Shape Pos a))"
          ++ "   : Free Shape Pos (List Shape Pos (List Shape Pos a))"
          ++ "   := @Cons Shape Pos (List Shape Pos a) xs"
          ++ "        (xs >>= (fun (xs_0 : List Shape Pos a) =>"
          ++ "           @tails_0 Shape Pos a xs_0))."

  it "translates recursive functions with outer lambda abstractions correctly"
    $ shouldSucceedWith
    $ do
        "List"           <- defineTestTypeCon "List" 1
        ("nil" , "Nil" ) <- defineTestCon "Nil" 0 "forall a. List a"
        ("cons", "Cons") <- defineTestCon "Cons"
                                          2
                                          "forall a. a -> List a -> List a"
        "append" <- defineTestFunc "append"
                                   1
                                   "forall a. List a -> List a -> List a"
        shouldConvertWithHelpersTo
            [ "append @a (xs :: List a) :: List a -> List a"
              ++ "  = \\(ys :: List a) -> case xs of {"
              ++ "      Nil        -> ys;"
              ++ "      Cons x xs' -> Cons @a x (append @a xs' ys)"
              ++ "    }"
            ]
          $  "(* Helper functions for append *) "
          ++ "Fixpoint append_0 (Shape : Type) (Pos : Shape -> Type)"
          ++ "                  {a : Type}"
          ++ "                  (xs : List Shape Pos a)"
          ++ "                  (ys : Free Shape Pos (List Shape Pos a))"
          ++ "                  {struct xs}"
          ++ " := match xs with"
          ++ "    | nil        => ys"
          ++ "    | cons x xs' => @Cons Shape Pos a x"
          ++ "        ((fun (ys0 : Free Shape Pos (List Shape Pos a)) =>"
          ++ "            xs' >>= (fun (xs'_0 : List Shape Pos a) =>"
          ++ "              @append_0 Shape Pos a xs'_0 ys0)) ys)"
          ++ "    end. "
          ++ "Definition append (Shape : Type) (Pos : Shape -> Type)"
          ++ "  {a : Type}"
          ++ "  (xs : Free Shape Pos (List Shape Pos a))"
          ++ "  : Free Shape Pos (Free Shape Pos (List Shape Pos a)"
          ++ "                 -> Free Shape Pos (List Shape Pos a))"
          ++ "  := pure (fun (ys : Free Shape Pos (List Shape Pos a)) =>"
          ++ "       xs >>= (fun (xs_0 : List Shape Pos a) =>"
          ++ "         @append_0 Shape Pos a xs_0 ys)). "

  it "translates recursive functions with nested lambda abstractions correctly"
    $ shouldSucceedWith
    $ do
        "List"           <- defineTestTypeCon "List" 1
        ("nil" , "Nil" ) <- defineTestCon "Nil" 0 "forall a. List a"
        ("cons", "Cons") <- defineTestCon "Cons"
                                          2
                                          "forall a. a -> List a -> List a"
        "bar" <- defineTestFunc "bar" 1 "forall a. (a -> List a) -> List a"
        "foo" <- defineTestFunc "foo" 1 "forall a. List a -> List a"
        shouldConvertWithHelpersTo
            [ "foo @a (xs :: List a) :: List a = bar @a (\\(y :: a) -> "
              ++ "case xs of {"
              ++ "  Nil -> Nil @a;"
              ++ "  Cons x xs' -> Cons @a y (foo @a xs')"
              ++ "})"
            ]
          $  "(* Helper functions for foo *) "
          ++ "Fixpoint foo_0 (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (xs : List Shape Pos a)"
          ++ "  (y : Free Shape Pos a) {struct xs}"
          ++ " := match xs with"
          ++ "    | nil => @Nil Shape Pos a"
          ++ "    | cons x xs' => @Cons Shape Pos a y (@bar Shape Pos a"
          ++ "        (pure (fun (y0 : Free Shape Pos a) => xs' >>="
          ++ "           (fun (xs'_0 : List Shape Pos a) =>"
          ++ "             @foo_0 Shape Pos a xs'_0 y0))))"
          ++ "    end. "
          ++ "Definition foo (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (xs : Free Shape Pos (List Shape Pos a))"
          ++ " : Free Shape Pos (List Shape Pos a)"
          ++ " := @bar Shape Pos a (pure (fun (y : Free Shape Pos a) =>"
          ++ "      xs >>= (fun (xs_0 : List Shape Pos a) =>"
          ++ "        @foo_0 Shape Pos a xs_0 y)))."

  it
      "translates recursive functions with nested pattern matching on recursive argument correctly"
    $ shouldSucceedWith
    $ do
        "List"           <- defineTestTypeCon "List" 1
        ("nil" , "Nil" ) <- defineTestCon "Nil" 0 "forall a. List a"
        ("cons", "Cons") <- defineTestCon "Cons"
                                          2
                                          "forall a. a -> List a -> List a"
        "last" <- definePartialTestFunc "last" 1 "forall a. List a -> a"
        shouldConvertWithHelpersTo
            [ "last @a (xs :: List a) :: a = case xs of {"
              ++ "    Nil       -> undefined @a;"
              ++ "     Cons x xs' -> case xs' of {"
              ++ "                     Nil        -> x;"
              ++ "                     Cons y ys  -> last @a ys"
              ++ "                   }"
              ++ "  }"
            ]
          $  "(* Helper functions for last *) "
          ++ "Fixpoint last_0 (Shape : Type) (Pos : Shape -> Type)"
          ++ "  (P : Partial Shape Pos) {a : Type}"
          ++ "  (xs : List Shape Pos a) {struct xs}"
          ++ " := match xs with"
          ++ "    | nil        => @undefined Shape Pos P a"
          ++ "    | cons x xs' =>"
          ++ "        xs' >>= (fun xs'_0 =>"
          ++ "            match xs'_0 with"
          ++ "            | nil       => x"
          ++ "            | cons y ys => ys >>="
          ++ "                 (fun (ys_0 : List Shape Pos a) =>"
          ++ "                    @last_0 Shape Pos P a ys_0)"
          ++ "            end)"
          ++ "    end. "
          ++ "Definition last (Shape : Type) (Pos : Shape -> Type)"
          ++ "  (P : Partial Shape Pos) {a : Type}"
          ++ "  (xs : Free Shape Pos (List Shape Pos a))"
          ++ " : Free Shape Pos a"
          ++ " := xs >>= (fun (xs_0 : List Shape Pos a) =>"
          ++ "      @last_0 Shape Pos P a xs_0)."

  it "allows the arguments of helper functions to be shadowed"
    $ shouldSucceedWith
    $ do
        "Integer"        <- defineTestTypeCon "Integer" 0
        "succ"           <- defineTestFunc "succ" 1 "Integer -> Integer"
        "List"           <- defineTestTypeCon "List" 1
        ("nil" , "Nil" ) <- defineTestCon "Nil" 0 "forall a. List a"
        ("cons", "Cons") <- defineTestCon "Cons"
                                          2
                                          "forall a. a -> List a -> List a"
        "length" <- defineTestFunc "length" 1 "forall a. List a -> Integer"
        shouldConvertWithHelpersTo
            [ "length @a (xs :: List a) :: Integer"
              ++ "  = case xs of {"
              ++ "    Nil        -> 0;"
              ++ "    Cons x xs -> succ (length @a xs)"
              ++ "  }"
            ]
          $  "(* Helper functions for length *) "
          ++ "Fixpoint length_0 (Shape : Type) (Pos : Shape -> Type)"
          ++ "  {a : Type} (xs : List Shape Pos a) {struct xs}"
          ++ " := match xs with"
          ++ "    | nil => pure 0%Z"
          ++ "    | cons x xs0 => succ Shape Pos"
          ++ "        (xs0 >>= (fun (xs0_0 : List Shape Pos a) =>"
          ++ "             @length_0 Shape Pos a xs0_0))"
          ++ "    end. "
          ++ "Definition length (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (xs : Free Shape Pos (List Shape Pos a))"
          ++ "  : Free Shape Pos (Integer Shape Pos)"
          ++ " := xs >>= (fun (xs_0 : List Shape Pos a) =>"
          ++ "    @length_0 Shape Pos a xs_0)."

  it "does not pass shadowed arguments of main function to helper functions"
    $ shouldSucceedWith
    $ do
        "Integer"        <- defineTestTypeCon "Integer" 0
        "succ"           <- defineTestFunc "succ" 1 "Integer -> Integer"
        "List"           <- defineTestTypeCon "List" 1
        ("nil" , "Nil" ) <- defineTestCon "Nil" 0 "forall a. List a"
        ("cons", "Cons") <- defineTestCon "Cons"
                                          2
                                          "forall a. a -> List a -> List a"
        "foo" <- defineTestFunc "foo" 1 "forall a. Integer -> List a -> Integer"
        shouldConvertWithHelpersTo
            [ "foo @a (n :: Integer) (xs :: List a) :: Integer"
              ++ "  = (\\(n :: Integer) -> case xs of {"
              ++ "      Nil        -> n;"
              ++ "      Cons x xs' -> foo @a n xs';"
              ++ "    }) (succ n)"
            ]
          $  "(* Helper functions for foo *) "
          ++ "Fixpoint foo_0 (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (n : Free Shape Pos (Integer Shape Pos))"
          ++ "  (xs : List Shape Pos a) {struct xs}"
          ++ " := match xs with"
          ++ "    | nil => n"
          ++ "    | cons x xs' =>"
          ++ "        (fun (n0 : Free Shape Pos (Integer Shape Pos)) =>"
          ++ "           xs' >>= (fun (xs'_0 : List Shape Pos a) =>"
          ++ "           @foo_0 Shape Pos a n0 xs'_0))"
          ++ "        (succ Shape Pos n)"
          ++ "    end. "
          ++ "Definition foo (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (n : Free Shape Pos (Integer Shape Pos))"
          ++ "  (xs : Free Shape Pos (List Shape Pos a))"
          ++ " : Free Shape Pos (Integer Shape Pos)"
          ++ "  := (fun (n0 : Free Shape Pos (Integer Shape Pos)) =>"
          ++ "        xs >>= (fun (xs_0 : List Shape Pos a) =>"
          ++ "        @foo_0 Shape Pos a n0 xs_0))"
          ++ "     (succ Shape Pos n)."

  it "translates polymorphically recursive functions correctly"
    $ shouldSucceedWith
    $ do
        "Integer"        <- defineTestTypeCon "Integer" 0
        "succ"           <- defineTestFunc "succ" 1 "Integer -> Integer"
        "Pair"           <- defineTestTypeCon "Pair" 2
        "Tree"           <- defineTestTypeCon "Tree" 1
        ("leaf", "Leaf") <- defineTestCon "Leaf" 1 "forall a. a -> Tree a"
        ("fork", "Fork") <- defineTestCon "Fork"
                                          1
                                          "forall a. Tree (Pair a) -> Tree a"
        "height" <- defineTestFunc "height" 1 "forall a. Tree a -> Integer"
        shouldConvertWithHelpersTo
            [ "height @a (t :: Tree a) :: Integer = case t of {"
              ++ "    Leaf x  -> 1;"
              ++ "    Fork t' -> succ (height @(Pair a a) t');"
              ++ "  }"
            ]
          $  "(* Helper functions for height *) "
          ++ "Fixpoint height_0 (Shape : Type) (Pos : Shape -> Type)"
          ++ "  {a : Type} (t : Tree Shape Pos a) {struct t}"
          ++ " := match t with"
          ++ "     | leaf x => pure 1%Z"
          ++ "     | fork t' => succ Shape Pos"
          ++ "         (t' >>="
          ++ "           (fun (t'_0 : Tree Shape Pos (Pair Shape Pos a a)) =>"
          ++ "              @height_0 Shape Pos (Pair Shape Pos a a) t'_0))"
          ++ "     end. "
          ++ "Definition height (Shape : Type) (Pos : Shape -> Type)"
          ++ "  {a : Type} (t : Free Shape Pos (Tree Shape Pos a))"
          ++ "  : Free Shape Pos (Integer Shape Pos)"
          ++ " := t >>= (fun (t_0 : Tree Shape Pos a) =>"
          ++ "      @height_0 Shape Pos a t_0)."

  it "translates recursive functions with one strict argument correctly"
    $ shouldSucceedWith
    $ do
        "Integer"        <- defineTestTypeCon "Integer" 0
        "succ"           <- defineTestFunc "succ" 1 "Integer -> Integer"
        "List"           <- defineTestTypeCon "List" 1
        ("nil" , "Nil" ) <- defineTestCon "Nil" 0 "forall a. List a"
        ("cons", "Cons") <- defineTestCon "Cons"
                                          2
                                          "forall a. a -> List a -> List a"
        "length" <- defineStrictTestFunc "length"
                                         [True]
                                         "forall a. List a -> Integer"
        shouldConvertWithHelpersTo
            [ "length @a !(xs :: List a) :: Integer = case xs of {"
              ++ "    Nil        -> 0;"
              ++ "    Cons x xs' -> succ (length @a xs')"
              ++ "  }"
            ]
          $  "(* Helper functions for length *) "
          ++ "Fixpoint length_0 (Shape : Type) (Pos : Shape -> Type)"
          ++ "  {a : Type} (xs : List Shape Pos a) {struct xs}"
          ++ " := match xs with"
          ++ "    | nil        => pure 0%Z"
          ++ "    | cons x xs' => succ Shape Pos"
          ++ "         (xs' >>= (fun (xs'_0 : List Shape Pos a) =>"
          ++ "           @length_0 Shape Pos a xs'_0))"
          ++ "    end. "
          ++ "Definition length (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (xs : List Shape Pos a)"
          ++ "  : Free Shape Pos (Integer Shape Pos)"
          ++ " := @length_0 Shape Pos a xs."

  it
      "translates recursive functions with strict and non-strict arguments correctly"
    $ shouldSucceedWith
    $ do
        "List"           <- defineTestTypeCon "List" 1
        ("nil" , "Nil" ) <- defineTestCon "Nil" 0 "forall a. List a"
        ("cons", "Cons") <- defineTestCon "Cons"
                                          2
                                          "forall a. a -> List a -> List a"
        "interleave" <- defineStrictTestFunc
          "interleave"
          [False, True]
          "forall a. List a -> List a -> List a"
        shouldConvertWithHelpersTo
            [ "interleave @a (xs :: List a) !(ys :: List a) :: List a ="
              ++ "  case xs of {"
              ++ "    Cons x xs' ->"
              ++ "      case ys of {"
              ++ "        Cons y ys' ->"
              ++ "          Cons @a x (Cons @a y (interleave @a xs' ys'));"
              ++ "        Nil        -> xs"
              ++ "      };"
              ++ "    Nil        -> ys"
              ++ "  }"
            ]
          $  "(* Helper functions for interleave *) "
          ++ "Fixpoint interleave_0 (Shape : Type) (Pos : Shape -> Type)"
          ++ "  {a : Type} (xs : List Shape Pos a) (ys : List Shape Pos a)"
          ++ "  {struct xs}"
          ++ " := match xs with"
          ++ "    | cons x xs' =>"
          ++ "        match ys with"
          ++ "        | cons y ys' =>"
          ++ "            @Cons Shape Pos a x"
          ++ "              (@Cons Shape Pos a y"
          ++ "                (xs' >>= (fun (xs'_0 : List Shape Pos a) =>"
          ++ "                  ys' >>= (fun (ys'_0 : List Shape Pos a) =>"
          ++ "                    @interleave_0 Shape Pos a xs'_0 ys'_0))))"
          ++ "        | nil => pure xs"
          ++ "        end"
          ++ "    | nil => pure ys"
          ++ "    end. "
          ++ "Definition interleave (Shape : Type) (Pos : Shape -> Type)"
          ++ "  {a : Type} (xs : Free Shape Pos (List Shape Pos a))"
          ++ "  (ys : List Shape Pos a) : Free Shape Pos (List Shape Pos a)"
          ++ " := xs >>= (fun (xs_0 : List Shape Pos a) =>"
          ++ "             @interleave_0 Shape Pos a xs_0 ys)."
  it
      "converts recursive functions with a strict argument preceding the decreasing argument correctly"
    $ shouldSucceedWith
    $ do
        "List"           <- defineTestTypeCon "List" 1
        ("nil" , "Nil" ) <- defineTestCon "Nil" 0 "forall a. List a"
        ("cons", "Cons") <- defineTestCon "Cons"
                                          2
                                          "forall a. a -> List a -> List a"
        "foo" <- defineStrictTestFunc "foo"
                                      [True, False]
                                      "forall a. a -> List a -> a"
        shouldConvertWithHelpersTo
            [ "foo @a !(x :: a) (xs :: List a) :: a ="
              ++ "  case xs of {"
              ++ "    Cons x' xs' -> foo @a x xs';"
              ++ "    Nil         -> x"
              ++ "  }"
            ]
          $  "(* Helper functions for foo *) "
          ++ "Fixpoint foo_0 (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (x : a) (xs : List Shape Pos a) {struct xs}"
          ++ " := match xs with"
          ++ "    | cons x' xs' => xs' >>= (fun (xs'_0 : List Shape Pos a) =>"
          ++ "                                @foo_0 Shape Pos a x xs'_0)"
          ++ "    | nil => pure x"
          ++ "    end. "
          ++ "Definition foo (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (x : a) (xs : Free Shape Pos (List Shape Pos a))"
          ++ "  : Free Shape Pos a"
          ++ " := xs >>= (fun (xs_0 : List Shape Pos a) =>"
          ++ "              @foo_0 Shape Pos a x xs_0)."
  it
      "translates recursive functions affected by the eta conversion pass correctly"
    $ shouldSucceedWith
    $ avoidLaziness
    $ do
        "List"           <- defineTestTypeCon "List" 1
        ("nil" , "Nil" ) <- defineTestCon "Nil" 0 "forall a. List a"
        ("cons", "Cons") <- defineTestCon "Cons"
                                          2
                                          "forall a. a -> List a -> List a"
        "Unit"       <- defineTestTypeCon "Unit" 0
        ("tt", "Tt") <- defineTestCon "Tt" 0 "Unit"
        "const"      <- defineTestFunc "const" 2 "forall a b. a -> b -> a"
        "append"     <- defineTestFunc
          "append"
          3
          "forall a b. List a -> List a -> b -> List a"
        shouldConvertWithHelpersTo
          [ "append @a @b (xs :: List a) (ys :: List a) :: b -> List a ="
            ++ "  \\y -> const @(List a) @b"
            ++ "    (case xs of {"
            ++ "      Nil      -> ys;"
            ++ "      Cons x xs' -> Cons @a x (append @a @Unit xs' ys Tt)"
            ++ "    } :: List a) y"
          ]
          (  "(* Helper functions for append *)"
          ++ " Fixpoint append_0"
          ++ "   (Shape : Type) (Pos : Shape -> Type) {a b : Type}"
          ++ "   (xs : List Shape Pos a) (ys : Free Shape Pos (List Shape Pos a))"
          ++ "   {struct xs} : Free Shape Pos (List Shape Pos a)"
          ++ "  := match xs with"
          ++ "     | nil => ys"
          ++ "     | cons x xs' =>"
          ++ "         @Cons Shape Pos a x"
          ++ "           ((fun y =>"
          ++ "               @const Shape Pos (List Shape Pos a) (Unit Shape Pos)"
          ++ "                 (xs' >>= (fun (xs'_0 : List Shape Pos a) =>"
          ++ "                   @append_0 Shape Pos a (Unit Shape Pos) xs'_0 ys))"
          ++ "                 y)"
          ++ "            (Tt Shape Pos))"
          ++ "     end."
          ++ " Definition append"
          ++ "   (Shape : Type) (Pos : Shape -> Type) {a b : Type}"
          ++ "   (xs : Free Shape Pos (List Shape Pos a))"
          ++ "   (ys : Free Shape Pos (List Shape Pos a))"
          ++ "   : Free Shape Pos (Free Shape Pos b -> Free Shape Pos (List Shape Pos a))"
          ++ "  := pure (fun y =>"
          ++ "       @const Shape Pos (List Shape Pos a) b"
          ++ "         (xs >>= (fun (xs_0 : List Shape Pos a) =>"
          ++ "           @append_0 Shape Pos a b xs_0 ys))"
          ++ "         y)."
          )

  it "fails when translating functions with arguments of unknown type"
    $ let
        res = do
          "List"           <- defineTestTypeCon "List" 1
          ("nil" , "Nil" ) <- defineTestCon "Nil" 0 "forall a. List a"
          ("cons", "Cons") <- defineTestCon "Cons"
                                            2
                                            "forall a. a -> List a -> List a"
          "const"  <- defineTestFunc "const" 2 "forall a b. a -> b -> a"
          "append" <- defineTestFunc
            "append"
            3
            "forall a b. List a -> List a -> b -> List a"
          input <- mapM
            parseTestFuncDecl
            [ "append @a @b (xs :: List a) (ys :: List a) :: b -> List a ="
              ++ "  \\y -> const @(List a) @b"
              ++ "    (case xs of {"
              ++ "      Nil      -> ys;"
              ++ "      Cons x xs' -> Cons @a x (append @a @b xs' ys y)"
              ++ "    } :: List a) y"
            ]
          convertRecFuncDeclsWithHelpers input
      in  shouldThrow (avoidLaziness res) (errorCall "Maybe.fromJust: Nothing")
