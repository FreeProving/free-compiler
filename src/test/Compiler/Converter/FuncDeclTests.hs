module Compiler.Converter.FuncDeclTests where

import           Test.Hspec

import           Compiler.Util.Test

-------------------------------------------------------------------------------
-- Non-recursive function declarations                                       --
-------------------------------------------------------------------------------

-- | Test group for 'convertNonRecFuncDecl' tests.
testConvertNonRecFuncDecl :: Spec
testConvertNonRecFuncDecl =
  describe "Compiler.Converter.FuncDecl.convertNonRecursiveFunction" $ do
    it "translates 0-ary functions (pattern-bindings) correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo ["foo :: Integer", "foo = 42"]
            $  "Definition foo (Shape : Type) (Pos : Shape -> Type)"
            ++ "  : Free Shape Pos (Integer Shape Pos)"
            ++ "  := pure 42%Z."

    it "translates 0-ary functions that return functions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo ["foo :: a -> Integer", "foo = \\x -> 42"]
            $  "Definition foo (Shape : Type) (Pos : Shape -> Type) {a : Type}"
            ++ "  (x : Free Shape Pos a)"
            ++ "  : Free Shape Pos (Integer Shape Pos)"
            ++ "  := pure 42%Z."

    it "translates functions that return functions correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo
              ["foo :: a -> b -> Integer", "foo x = \\y -> 42"]
            $  "Definition foo (Shape : Type) (Pos : Shape -> Type)"
            ++ "  {a b : Type} (x : Free Shape Pos a) (y : Free Shape Pos b)"
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

    it "allows the function arguments to be shadowed"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo
              [ "tail :: [a] -> [a]"
              , "tail xs = case xs of { [] -> undefined; x : xs -> xs }"
              ]
            $  "Definition tail (Shape : Type) (Pos : Shape -> Type)"
            ++ "  (P : Partial Shape Pos) {a : Type}"
            ++ "  (xs : Free Shape Pos (List Shape Pos a))"
            ++ "  : Free Shape Pos (List Shape Pos a)"
            ++ " := xs >>= (fun xs_0 =>"
            ++ "    match xs_0 with"
            ++ "    | nil       => undefined"
            ++ "    | cons x xs0 => xs0"
            ++ "    end)."

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
          [ "fac :: Integer -> Integer"
          , "fac n = if n == 0 then 1 else n * fac (n - 1)"
          ]

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

    it "translates partial recursive functions correctly"
      $  shouldSucceed
      $  fromConverter
      $  shouldTranslateDeclsTo
           [ "findJust :: (a -> Bool) -> [a] -> a"
           , "findJust p xs = case xs of {"
           ++ "  []      -> undefined;"
           ++ "  x : xs' -> if p x then x else findJust p xs'"
           ++ "}"
           ]
      $  "Section section_findJust_0. "
      ++ "(* Constant arguments for findJust *) "
      ++ "Variable Shape : Type. "
      ++ "Variable Pos : Shape -> Type. "
      ++ "Variable a : Type. "
      ++ "Variable p_0 : Free Shape Pos"
      ++ "  (Free Shape Pos a -> Free Shape Pos (Bool Shape Pos)). "
      ++ "(* Helper functions for findJust *) "
      ++ "Fixpoint findJust_0 (P : Partial Shape Pos)"
      ++ "  (xs : List Shape Pos a) {struct xs}"
      ++ "  := match xs with"
      ++ "     | nil            => undefined"
      ++ "     | cons x_0 xs'_0 =>"
      ++ "        (p_0 >>= (fun p_1 => p_1 x_0)) >>="
      ++ "        (fun (cond_0 : Bool Shape Pos) =>"
      ++ "           if cond_0"
      ++ "           then x_0"
      ++ "           else xs'_0 >>= (fun (xs'_1 : List Shape Pos a) =>"
      ++ "                      findJust_0 P xs'_1))"
      ++ "     end. "
      ++ "Definition findJust (P : Partial Shape Pos)"
      ++ "  (xs : Free Shape Pos (List Shape Pos a))"
      ++ "  : Free Shape Pos a"
      ++ "  := xs >>= (fun (xs_0 : List Shape Pos a) =>"
      ++ "          findJust_0 P xs_0). "
      ++ "End section_findJust_0. "
      ++ "Arguments findJust Shape Pos P {a}."

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
      ++ "  := match xs with"
      ++ "     | nil        => True_ Shape Pos"
      ++ "     | cons x xs' =>"
      ++ "         xs' >>= (fun (xs'_0 : List Shape Pos a) =>"
      ++ "           odd_len_0 Shape Pos xs'_0)"
      ++ "     end "
      ++ "with odd_len_0 (Shape : Type) (Pos : Shape -> Type) {a : Type}"
      ++ "  (xs : List Shape Pos a)"
      ++ "  {struct xs}"
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
      $  "Section section_append_0. "
      ++ "(* Constant arguments for append *) "
      ++ "Variable Shape : Type. "
      ++ "Variable Pos : Shape -> Type. "
      ++ "Variable a : Type. "
      ++ "Variable ys_0 : Free Shape Pos (List Shape Pos a). "
      ++ "(* Helper functions for append *) "
      ++ "Fixpoint append_0 (xs : List Shape Pos a) {struct xs}"
      ++ " := match xs with"
      ++ "    | nil            => ys_0"
      ++ "    | cons x_0 xs'_0 => Cons Shape Pos x_0 (xs'_0 >>="
      ++ "      (fun (xs'_1 : List Shape Pos a) =>"
      ++ "          append_0 xs'_1))"
      ++ "    end. "
      ++ "Definition append (xs : Free Shape Pos (List Shape Pos a))"
      ++ " : Free Shape Pos (List Shape Pos a)"
      ++ " := xs >>= (fun (xs_0 : List Shape Pos a) =>"
      ++ "   append_0 xs_0). "
      ++ "End section_append_0. "
      ++ "Arguments append Shape Pos {a}."

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

    it
        "translates recursive functions with nested pattern matching on recursive argument correctly"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo
              [ "last :: [a] -> a"
              , "last xs = case xs of {"
              ++ "  []       -> undefined;"
              ++ "   x : xs' -> case xs of {"
              ++ "     []      -> undefined;"
              ++ "     y : ys  -> last ys"
              ++ "   }"
              ++ "}"
              ]
            $  "(* Helper functions for last *) "
            ++ "Fixpoint last_0 (Shape : Type) (Pos : Shape -> Type)"
            ++ "  (P : Partial Shape Pos) {a : Type}"
            ++ "  (xs : List Shape Pos a) {struct xs}"
            ++ " := match xs with"
            ++ "    | nil        => undefined"
            ++ "    | cons x xs' =>"
            ++ "        match xs with"
            ++ "        | nil       => undefined"
            ++ "        | cons y ys => ys >>="
            ++ "            (fun (ys_0 : List Shape Pos a) => "
            ++ "               last_0 Shape Pos P ys_0)"
            ++ "        end"
            ++ "    end. "
            ++ "Definition last (Shape : Type) (Pos : Shape -> Type)"
            ++ "  (P : Partial Shape Pos) {a : Type}"
            ++ "  (xs : Free Shape Pos (List Shape Pos a))"
            ++ " : Free Shape Pos a"
            ++ " := xs >>= (fun (xs_0 : List Shape Pos a) =>"
            ++ "      last_0 Shape Pos P xs_0)."

    it "allows the arguments of helper functions to be shadowed"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo
              [ "length :: [a] -> Integer"
              , "length xs = case xs of { [] -> 0; x : xs -> length xs + 1 }"
              ]
            $  "(* Helper functions for length *) "
            ++ "Fixpoint length_0 (Shape : Type) (Pos : Shape -> Type)"
            ++ "  {a : Type} (xs : List Shape Pos a) {struct xs}"
            ++ " := match xs with"
            ++ "    | nil => pure 0%Z"
            ++ "    | cons x xs0 => addInteger Shape Pos"
            ++ "        (xs0 >>= (fun (xs0_0 : List Shape Pos a) =>"
            ++ "             length_0 Shape Pos xs0_0))"
            ++ "        (pure 1%Z)"
            ++ "    end. "
            ++ "Definition length (Shape : Type) (Pos : Shape -> Type) {a : Type}"
            ++ "  (xs : Free Shape Pos (List Shape Pos a))"
            ++ "  : Free Shape Pos (Integer Shape Pos)"
            ++ " := xs >>= (fun (xs_0 : List Shape Pos a) =>"
            ++ "    length_0 Shape Pos xs_0)."

    it "does not pass shaodwed arguments of main function to helper functions"
      $ shouldSucceed
      $ fromConverter
      $ do
          shouldTranslateDeclsTo
              [ "take :: Integer -> [a] -> [a]"
              , "take n xs ="
              ++ "(\\n -> case xs of { [] -> []; x : xs' -> take (n - 1) xs' })"
              ++ " n"
              ]
            $  "(* Helper functions for take *) "
            ++ "Fixpoint take_0 (Shape : Type) (Pos : Shape -> Type)"
            ++ "  {a : Type} n (xs : List Shape Pos a) {struct xs}"
            ++ " := match xs with"
            ++ "    | nil => Nil Shape Pos"
            ++ "    | cons x xs' =>"
            ++ "        (fun n_3 => xs' >>= (fun (xs'_0 : List Shape Pos a) =>"
            ++ "           take_0 Shape Pos"
            ++ "             n_3"
            ++ "             xs'_0))"
            ++ "        (subInteger Shape Pos n (pure 1%Z))"
            ++ "    end. "
            ++ "Definition take (Shape : Type) (Pos : Shape -> Type)"
            ++ "  {a : Type} (n : Free Shape Pos (Integer Shape Pos))"
            ++ "  (xs : Free Shape Pos (List Shape Pos a))"
            ++ " : Free Shape Pos (List Shape Pos a)"
            ++ " := (fun n0 => xs >>= (fun (xs_0 : List Shape Pos a) =>"
            ++ "       take_0 Shape Pos n0 xs_0)) n."
