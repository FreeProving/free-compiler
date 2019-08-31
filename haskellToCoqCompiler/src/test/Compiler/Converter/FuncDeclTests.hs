module Compiler.Converter.FuncDeclTests where

import           Test.Hspec

import           Compiler.Util.Test

-------------------------------------------------------------------------------
-- Non-recursive function declarations                                       --
-------------------------------------------------------------------------------

-- | Test group for 'convertNonRecFuncDecl' tests.
testConvertNonRecFuncDecl :: Spec
testConvertNonRecFuncDecl =
  describe "FuncDecl.convertNonRecursiveFunction" $ do
    it "translates 0-ary functions (pattern-bindings) correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo ["foo :: Integer", "foo = 42"]
            $  "Definition foo (Shape : Type) (Pos : Shape -> Type)"
            ++ "  : Free Shape Pos (Integer Shape Pos)"
            ++ "  := pure 42%Z."

    it "translates polymorphic functions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo ["foo :: a -> a", "foo x = x"]
            $  "Definition foo (Shape : Type) (Pos : Shape -> Type) {a : Type}"
            ++ "  (x : Free Shape Pos a) : Free Shape Pos a := x."

    it "translates functions with multiple arguments correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo ["foo :: a -> b -> (a, b)", "foo x y = (x, y)"]
            $ "Definition foo (Shape : Type) (Pos : Shape -> Type) {a b : Type}"
            ++ "  (x : Free Shape Pos a) (y : Free Shape Pos b)"
            ++ "  : Free Shape Pos (Pair Shape Pos a b)"
            ++ "  := Pair_ Shape Pos x y."

    it "translates higher order functions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo
              [ "curry :: ((a, b) -> c) -> a -> b -> c"
              , "curry f x y = f (x, y)"
              ]
            $  "Definition curry (Shape : Type) (Pos : Shape -> Type)"
            ++ "  {a b c : Type}"
            ++ "  (f : Free Shape Pos (Free Shape Pos (Pair Shape Pos a b)"
            ++ "    -> Free Shape Pos c))"
            ++ "  (x : Free Shape Pos a)"
            ++ "  (y : Free Shape Pos b)"
            ++ "  : Free Shape Pos c"
            ++ "  := f >>= (fun f_0 => f_0 (Pair_ Shape Pos x y))."

    it "translates partial functions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo
              [ "head :: [a] -> a"
              , "head xs = case xs of { [] -> undefined; x : xs' -> x }"
              ]
            $  "Definition head (Shape : Type) (Pos : Shape -> Type)"
            ++ "  (P : Partial Shape Pos) {a : Type}"
            ++ "  (xs : Free Shape Pos (List Shape Pos a))"
            ++ "  : Free Shape Pos a"
            ++ "  := xs >>= (fun xs_0 =>"
            ++ "       match xs_0 with"
            ++ "       | nil        => undefined"
            ++ "       | cons x xs' => x"
            ++ "       end)."

-------------------------------------------------------------------------------
-- Recursive function declarations                                           --
-------------------------------------------------------------------------------

-- | Test group for 'convertRecFuncDecls' tests.
testConvertRecFuncDecls :: Spec
testConvertRecFuncDecls =
  describe "Compiler.Converter.FuncDecl.convertRecFuncDecls" $ do
    it "requires at least one argument"
      $ shouldReportFatal
      $ fromConverter
      $ convertTestDecls ["loop :: a", "loop = loop"]

    it "requires a case expression (if expressions don't suffice)"
      $ shouldReportFatal
      $ fromConverter
      $ convertTestDecls
          ["fac :: Integer -> Integer", "fac n = if n == 0 then 1 else n * fac (n - 1)"]

    it "requires the case expression to match an argument"
      $ shouldReportFatal
      $ fromConverter
      $ do
          "f" <- defineTestFunc "f" 0 "()"
          convertTestDecls ["loop :: a", "loop = case f of () -> loop"]

    it "requires a decreasing argument" $ shouldReportFatal $ fromConverter $ do
      convertTestDecls ["loop :: a -> a", "loop x = case x of () -> loop x"]

    it "translates simple recursive functions correctly"
      $  shouldSucceed
      $  fromConverter
      $  shouldTranslateDeclsTo
           [ "length :: [a] -> Integer"
           , "length xs = case xs of { [] -> 0; x : xs' -> length xs' + 1 }"
           ]
      $  "(* Helper functions for length *) "
      ++ "Fixpoint length_0 (Shape : Type) (Pos : Shape -> Type) {a : Type}"
      ++ "  (xs : List Shape Pos a)"
      ++ "  {struct xs}"
      ++ "  : Free Shape Pos (Integer Shape Pos)"
      ++ "  := match xs with"
      ++ "     | nil        => pure 0%Z"
      ++ "     | cons x xs' => addInteger Shape Pos"
      ++ "         (xs' >>= (fun (xs'_0 : List Shape Pos a) =>"
      ++ "           length_0 Shape Pos xs'_0))"
      ++ "         (pure 1%Z)"
      ++ "     end. "
      ++ "Definition length (Shape : Type) (Pos : Shape -> Type) {a : Type}"
      ++ "  (xs : Free Shape Pos (List Shape Pos a))"
      ++ "  : Free Shape Pos (Integer Shape Pos)"
      ++ "  := xs >>= (fun (xs_0 : List Shape Pos a) =>"
      ++ "       length_0 Shape Pos xs_0)."

    it "translates mutually recursive functions correctly"
      $  shouldSucceed
      $  fromConverter
      $  shouldTranslateDeclsTo
           [ "even_len, odd_len :: [a] -> Bool"
           , "even_len xs = case xs of { [] -> True; x : xs' -> odd_len xs' }"
           , "odd_len xs = case xs of { [] -> False; x : xs' -> even_len xs' }"
           ]
      $  "(* Helper functions for even_len, odd_len *) "
      ++ "Fixpoint even_len_0 (Shape : Type) (Pos : Shape -> Type) {a : Type}"
      ++ "  (xs : List Shape Pos a)"
      ++ "  {struct xs}"
      ++ "  : Free Shape Pos (Bool Shape Pos)"
      ++ "  := match xs with"
      ++ "     | nil        => True_ Shape Pos"
      ++ "     | cons x xs' =>"
      ++ "         xs' >>= (fun (xs'_0 : List Shape Pos a) =>"
      ++ "           odd_len_0 Shape Pos xs'_0)"
      ++ "     end "
      ++ "with odd_len_0 (Shape : Type) (Pos : Shape -> Type) {a : Type}"
      ++ "  (xs : List Shape Pos a)"
      ++ "  {struct xs}"
      ++ "  : Free Shape Pos (Bool Shape Pos)"
      ++ "  := match xs with"
      ++ "     | nil        => False_ Shape Pos"
      ++ "     | cons x xs' =>"
      ++ "         xs' >>= (fun (xs'_0 : List Shape Pos a) =>"
      ++ "           even_len_0 Shape Pos xs'_0)"
      ++ "     end. "
      ++ "Definition even_len (Shape : Type) (Pos : Shape -> Type) {a : Type}"
      ++ "  (xs : Free Shape Pos (List Shape Pos a))"
      ++ "  : Free Shape Pos (Bool Shape Pos)"
      ++ "  := xs >>= (fun (xs_0 : List Shape Pos a) =>"
      ++ "           even_len_0 Shape Pos xs_0). "
      ++ "Definition odd_len (Shape : Type) (Pos : Shape -> Type) {a : Type}"
      ++ "  (xs : Free Shape Pos (List Shape Pos a))"
      ++ "  : Free Shape Pos (Bool Shape Pos)"
      ++ "  := xs >>= (fun (xs_0 : List Shape Pos a) =>"
      ++ "           odd_len_0 Shape Pos xs_0)."

    it "translates recursive functions with nested case expressions correctly"
      $  shouldSucceed
      $  fromConverter
      $  shouldTranslateDeclsTo
           [ "tails :: [a] -> [[a]]"
           , "tails xs = xs : case xs of { [] -> []; x : xs' -> tails xs' }"
           ]
      $  "(* Helper functions for tails *) "
      ++ "Fixpoint tails_0 (Shape : Type) (Pos : Shape -> Type) {a : Type}"
      ++ "  (xs : List Shape Pos a)"
      ++ "  {struct xs}"
      ++ "  : Free Shape Pos (List Shape Pos (List Shape Pos a))"
      ++ "  := match xs with"
      ++ "     | nil => Nil Shape Pos"
      ++ "     | cons x xs' => Cons Shape Pos xs'"
      ++ "         (xs' >>=  (fun (xs'_0 : List Shape Pos a) =>"
      ++ "            tails_0 Shape Pos xs'_0))"
      ++ "     end. "
      ++ " Definition tails (Shape : Type) (Pos : Shape -> Type) {a : Type}"
      ++ "   (xs : Free Shape Pos (List Shape Pos a))"
      ++ "   : Free Shape Pos (List Shape Pos (List Shape Pos a))"
      ++ "   := Cons Shape Pos xs (xs >>= (fun (xs_0 : List Shape Pos a) =>"
      ++ "        tails_0 Shape Pos xs_0))."

    it "translates recursive functions with outer lambda abstractions correctly"
      $  shouldSucceed
      $  fromConverter
      $  shouldTranslateDeclsTo
           [ "append :: [a] -> [a] -> [a]"
           , "append xs = \\ys -> "
             ++ "case xs of { [] -> ys; x : xs' -> x : append xs' ys }"
           ]
      $  "(* Helper functions for append *) "
      ++ "Fixpoint append_0 (Shape : Type) (Pos : Shape -> Type) {a : Type}"
      ++ "  (xs : List Shape Pos a) (ys : Free Shape Pos (List Shape Pos a))"
      ++ "  {struct xs}"
      ++ " : Free Shape Pos (List Shape Pos a)"
      ++ " := match xs with"
      ++ "    | nil        => ys"
      ++ "    | cons x xs' => Cons Shape Pos x (xs' >>="
      ++ "      (fun (xs'_0 : List Shape Pos a) => append_0 Shape Pos xs'_0 ys))"
      ++ "    end. "
      ++ "Definition append (Shape : Type) (Pos : Shape -> Type) {a : Type}"
      ++ "  (xs : Free Shape Pos (List Shape Pos a))"
      ++ "  (ys : Free Shape Pos (List Shape Pos a))"
      ++ " : Free Shape Pos (List Shape Pos a)"
      ++ " := xs >>= (fun (xs_0 : List Shape Pos a) =>"
      ++ "   append_0 Shape Pos xs_0 ys)."

    it
        "translates recursive functions with nested lambda abstractions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          "bar" <- defineTestFunc "bar" 1 "(a -> [a]) -> [a]"
          shouldTranslateDeclsTo
              [ "foo :: [a] -> [a]"
              , "foo xs = bar (\\y -> "
                ++ "case xs of { [] -> []; x : xs' -> y : foo xs' })"
              ]
            $  "(* Helper functions for foo *) "
            ++ "Fixpoint foo_0 (Shape : Type) (Pos : Shape -> Type) {a : Type}"
            ++ "  (xs : List Shape Pos a) y {struct xs}"
            ++ " : Free Shape Pos (List Shape Pos a)"
            ++ " := match xs with"
            ++ "    | nil => Nil Shape Pos"
            ++ "    | cons x xs' => Cons Shape Pos y (bar Shape Pos"
            ++ "        (pure (fun y_1 => xs' >>="
            ++ "           (fun (xs'_0 : List Shape Pos a) =>"
            ++ "             foo_0 Shape Pos xs'_0 y_1))))"
            ++ "    end. "
            ++ "Definition foo (Shape : Type) (Pos : Shape -> Type) {a : Type}"
            ++ "  (xs : Free Shape Pos (List Shape Pos a))"
            ++ " : Free Shape Pos (List Shape Pos a)"
            ++ " := bar Shape Pos (pure (fun y => xs >>="
            ++ "      (fun (xs_0 : List Shape Pos a) =>"
            ++ "        foo_0 Shape Pos xs_0 y)))."
