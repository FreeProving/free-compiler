module FreeC.Backend.Coq.Converter.FuncDeclTests where

import           Test.Hspec

import           FreeC.Util.Test

-------------------------------------------------------------------------------
-- Non-recursive function declarations                                       --
-------------------------------------------------------------------------------

-- | Test group for 'convertNonRecFuncDecl' tests.
testConvertNonRecFuncDecl :: Spec
testConvertNonRecFuncDecl =
  describe "FreeC.Backend.Coq.Converter.FuncDecl.convertNonRecursiveFunction"
    $ do
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
                $ "Definition foo (Shape : Type) (Pos : Shape -> Type) {a : Type}"
                ++ "  : Free Shape Pos (Free Shape Pos a"
                ++ "                 -> Free Shape Pos (Integer Shape Pos))"
                ++ "  := pure (fun (x : Free Shape Pos a) => pure 42%Z)."

        it "translates functions that return functions correctly"
          $ shouldSucceed
          $ fromConverter
          $ do
              shouldTranslateDeclsTo
                  ["foo :: a -> b -> Integer", "foo x = \\y -> 42"]
                $  "Definition foo (Shape : Type) (Pos : Shape -> Type)"
                ++ "  {a b : Type} (x : Free Shape Pos a)"
                ++ "  : Free Shape Pos (Free Shape Pos b"
                ++ "                 -> Free Shape Pos (Integer Shape Pos))"
                ++ "  := pure (fun (y : Free Shape Pos b) => pure 42%Z)."

        it "translates polymorphic functions correctly"
          $ shouldSucceed
          $ fromConverter
          $ do
              shouldTranslateDeclsTo ["foo :: a -> a", "foo x = x"]
                $ "Definition foo (Shape : Type) (Pos : Shape -> Type) {a : Type}"
                ++ "  (x : Free Shape Pos a) : Free Shape Pos a := x."

        it "translates functions with multiple arguments correctly"
          $ shouldSucceed
          $ fromConverter
          $ do
              shouldTranslateDeclsTo
                  ["foo :: a -> b -> (a, b)", "foo x y = (x, y)"]
                $ "Definition foo (Shape : Type) (Pos : Shape -> Type) {a b : Type}"
                ++ "  (x : Free Shape Pos a) (y : Free Shape Pos b)"
                ++ "  : Free Shape Pos (Pair Shape Pos a b)"
                ++ "  := @Pair_ Shape Pos a b x y."

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
                ++ "  := f >>= (fun f_0 => f_0 (@Pair_ Shape Pos a b x y))."

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
                ++ "       | nil        => @undefined Shape Pos P a"
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
                ++ "    | nil       => @undefined Shape Pos P (List Shape Pos a)"
                ++ "    | cons x xs0 => xs0"
                ++ "    end)."

        it "allows the type signature to be omitted"
          $ shouldSucceed
          $ fromConverter
          $ do
              shouldTranslateDeclsTo ["foo x = x"]
                $  "Definition foo (Shape : Type) (Pos : Shape -> Type)"
                ++ "  {t0 : Type} (x : Free Shape Pos t0)"
                ++ "  : Free Shape Pos t0"
                ++ " := x."

        it "does not allow duplicate type signatures"
          $ shouldReportFatal
          $ fromConverter
          $ do
              convertTestDecls
                ["foo :: ()", "foo :: Integer", "foo = undefined"]

        it "does not allow type signatures without function declaration"
          $ shouldReportFatal
          $ fromConverter
          $ do
              convertTestDecls
                ["foo :: ()", "foo :: Integer", "foo = undefined"]

-------------------------------------------------------------------------------
-- Recursive function declarations                                           --
-------------------------------------------------------------------------------

-- | Test group for 'convertRecFuncDecls' tests.
testConvertRecFuncDeclsWithHelpers :: Spec
testConvertRecFuncDeclsWithHelpers =
  describe "FreeC.Backend.Coq.Converter.FuncDecl.convertRecFuncDeclsWithHelpers"
    $ do
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

        it "requires a decreasing argument"
          $ shouldReportFatal
          $ fromConverter
          $ do
              convertTestDecls
                ["loop :: a -> a", "loop x = case x of () -> loop x"]

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
          ++ " : Free Shape Pos (Integer Shape Pos)"
          ++ "  := match xs with"
          ++ "     | nil        => pure 0%Z"
          ++ "     | cons x xs' => addInteger Shape Pos"
          ++ "         (xs' >>= (fun (xs'_0 : List Shape Pos a) =>"
          ++ "           @length_0 Shape Pos a xs'_0))"
          ++ "         (pure 1%Z)"
          ++ "     end. "
          ++ "Definition length (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (xs : Free Shape Pos (List Shape Pos a))"
          ++ "  : Free Shape Pos (Integer Shape Pos)"
          ++ "  := xs >>= (fun (xs_0 : List Shape Pos a) =>"
          ++ "       @length_0 Shape Pos a xs_0)."

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
          ++ "Variable a_0 : Type. "
          ++ "Variable p_0 : Free Shape Pos"
          ++ "  (Free Shape Pos a_0 -> Free Shape Pos (Bool Shape Pos)). "
          ++ "(* Helper functions for findJust *) "
          ++ "Fixpoint findJust_1 (P : Partial Shape Pos)"
          ++ "  (xs : List Shape Pos a_0) {struct xs}"
          ++ " : Free Shape Pos a_0"
          ++ "  := match xs with"
          ++ "     | nil            => @undefined Shape Pos P a_0"
          ++ "     | cons x xs' =>"
          ++ "        (p_0 >>= (fun p_1 => p_1 x)) >>="
          ++ "        (fun (cond_0 : Bool Shape Pos) =>"
          ++ "           if cond_0"
          ++ "           then x"
          ++ "           else xs' >>= (fun (xs'_0 : List Shape Pos a_0) =>"
          ++ "                      findJust_1 P xs'_0))"
          ++ "     end. "
          ++ "(* Main functions for findJust *) "
          ++ "Definition findJust_0 (P : Partial Shape Pos)"
          ++ "  (xs : Free Shape Pos (List Shape Pos a_0))"
          ++ "  : Free Shape Pos a_0"
          ++ "  := xs >>= (fun (xs_0 : List Shape Pos a_0) =>"
          ++ "          findJust_1 P xs_0). "
          ++ "End section_findJust_0. "
          ++ "Definition findJust (Shape : Type) (Pos : Shape -> Type)"
          ++ "  (P : Partial Shape Pos)"
          ++ "  {a : Type}"
          ++ "  (p : Free Shape Pos"
          ++ "         (Free Shape Pos a -> Free Shape Pos (Bool Shape Pos)))"
          ++ "  (xs : Free Shape Pos (List Shape Pos a))"
          ++ "  : Free Shape Pos a"
          ++ "  := findJust_0 Shape Pos a p P xs."

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
          ++ " : Free Shape Pos (Bool Shape Pos)"
          ++ "  := match xs with"
          ++ "     | nil        => True_ Shape Pos"
          ++ "     | cons x xs' =>"
          ++ "         xs' >>= (fun (xs'_0 : List Shape Pos a) =>"
          ++ "           @odd_len_0 Shape Pos a xs'_0)"
          ++ "     end "
          ++ "with odd_len_0 (Shape : Type) (Pos : Shape -> Type) {a : Type}"
          ++ "  (xs : List Shape Pos a)"
          ++ "  {struct xs}"
          ++ " : Free Shape Pos (Bool Shape Pos)"
          ++ "  := match xs with"
          ++ "     | nil        => False_ Shape Pos"
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

        it
            "translates recursive functions with nested case expressions correctly"
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
          ++ " : Free Shape Pos (List Shape Pos (List Shape Pos a))"
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

        it
            "translates recursive functions with outer lambda abstractions correctly"
          $  shouldSucceed
          $  fromConverter
          $  shouldTranslateDeclsTo
               [ "append :: [a] -> [a] -> [a]"
               , "append xs = \\ys -> "
                 ++ "case xs of { [] -> ys; x : xs' -> x : append xs' ys }"
               ]
          $  "(* Helper functions for append *) "
          ++ "Fixpoint append_0 (Shape : Type) (Pos : Shape -> Type)"
          ++ "                  {a : Type}"
          ++ "                  (xs : List Shape Pos a)"
          ++ "                  (ys : Free Shape Pos (List Shape Pos a))"
          ++ "                  {struct xs}"
          ++ "  : Free Shape Pos (List Shape Pos a)"
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
                ++ "  (xs : List Shape Pos a)"
                ++ "  (y : Free Shape Pos a) {struct xs}"
                ++ " : Free Shape Pos (List Shape Pos a)"
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
                ++ " : Free Shape Pos a"
                ++ " := match xs with"
                ++ "    | nil        => @undefined Shape Pos P a"
                ++ "    | cons x xs' =>"
                ++ "        match xs with"
                ++ "        | nil       => @undefined Shape Pos P a"
                ++ "        | cons y ys => ys >>="
                ++ "            (fun (ys_0 : List Shape Pos a) => "
                ++ "               @last_0 Shape Pos P a ys_0)"
                ++ "        end"
                ++ "    end. "
                ++ "Definition last (Shape : Type) (Pos : Shape -> Type)"
                ++ "  (P : Partial Shape Pos) {a : Type}"
                ++ "  (xs : Free Shape Pos (List Shape Pos a))"
                ++ " : Free Shape Pos a"
                ++ " := xs >>= (fun (xs_0 : List Shape Pos a) =>"
                ++ "      @last_0 Shape Pos P a xs_0)."

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
                ++ " : Free Shape Pos (Integer Shape Pos)"
                ++ " := match xs with"
                ++ "    | nil => pure 0%Z"
                ++ "    | cons x xs0 => addInteger Shape Pos"
                ++ "        (xs0 >>= (fun (xs0_0 : List Shape Pos a) =>"
                ++ "             @length_0 Shape Pos a xs0_0))"
                ++ "        (pure 1%Z)"
                ++ "    end. "
                ++ "Definition length (Shape : Type) (Pos : Shape -> Type) {a : Type}"
                ++ "  (xs : Free Shape Pos (List Shape Pos a))"
                ++ "  : Free Shape Pos (Integer Shape Pos)"
                ++ " := xs >>= (fun (xs_0 : List Shape Pos a) =>"
                ++ "    @length_0 Shape Pos a xs_0)."

        it
            "does not pass shadowed arguments of main function to helper functions"
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
                ++ "  {a : Type}"
                ++ "  (n : Free Shape Pos (Integer Shape Pos))"
                ++ "  (xs : List Shape Pos a) {struct xs}"
                ++ " : Free Shape Pos (List Shape Pos a)"
                ++ " := match xs with"
                ++ "    | nil => @Nil Shape Pos a"
                ++ "    | cons x xs' =>"
                ++ "        (fun (n0 : Free Shape Pos (Integer Shape Pos)) =>"
                ++ "           xs' >>= (fun (xs'_0 : List Shape Pos a) =>"
                ++ "             @take_0 Shape Pos a"
                ++ "               n0"
                ++ "               xs'_0))"
                ++ "        (subInteger Shape Pos n (pure 1%Z))"
                ++ "    end. "
                ++ "Definition take (Shape : Type) (Pos : Shape -> Type)"
                ++ "  {a : Type} (n : Free Shape Pos (Integer Shape Pos))"
                ++ "  (xs : Free Shape Pos (List Shape Pos a))"
                ++ " : Free Shape Pos (List Shape Pos a)"
                ++ " := (fun (n0 : Free Shape Pos (Integer Shape Pos)) =>"
                ++ "       xs >>= (fun (xs_0 : List Shape Pos a) =>"
                ++ "         @take_0 Shape Pos a n0 xs_0)) n."

        it "translates polymorphically recursive functions correctly"
          $ shouldSucceed
          $ fromConverter
          $ do
              "Tree"           <- defineTestTypeCon "Tree" 1
              ("leaf", "Leaf") <- defineTestCon "Leaf" 1 "a -> Tree a"
              ("fork", "Fork") <- defineTestCon "Fork" 1 "Tree (a, a) -> Tree a"
              shouldTranslateDeclsTo
                  [ "height :: Tree a -> Integer"
                  , "height t = case t of {"
                  ++ "    Leaf x -> 1;"
                  ++ "    Fork t' -> 1 + height t';"
                  ++ "  }"
                  ]
                $  "(* Helper functions for height *) "
                ++ "Fixpoint height_0 (Shape : Type) (Pos : Shape -> Type)"
                ++ "  {a : Type} (t : Tree Shape Pos a) {struct t}"
                ++ " : Free Shape Pos (Integer Shape Pos)"
                ++ " := match t with"
                ++ "     | leaf x => pure 1%Z"
                ++ "     | fork t' => addInteger Shape Pos (pure 1%Z)"
                ++ "         (t' >>="
                ++ "           (fun (t'_0 : Tree Shape Pos (Pair Shape Pos a a)) =>"
                ++ "              @height_0 Shape Pos (Pair Shape Pos a a) t'_0))"
                ++ "     end. "
                ++ "Definition height (Shape : Type) (Pos : Shape -> Type)"
                ++ "  {a : Type} (t : Free Shape Pos (Tree Shape Pos a))"
                ++ "  : Free Shape Pos (Integer Shape Pos)"
                ++ " := t >>= (fun (t_0 : Tree Shape Pos a) =>"
                ++ "      @height_0 Shape Pos a t_0)."

-------------------------------------------------------------------------------
-- Recursive function declarations with constant arguments                   --
-------------------------------------------------------------------------------

testConvertRecFuncDeclsWithSections :: Spec
testConvertRecFuncDeclsWithSections = do
  describe
      "FreeC.Backend.Coq.Converter.FuncDecl.convertRecFuncDeclsWithSections"
    $ do
        it "creates variable sentences for constant arguments"
          $  shouldSucceed
          $  fromConverter
          $  shouldTranslateDeclsTo
               [ "map :: (a -> b) -> [a] -> [b]"
               , "map f xs = case xs of { [] -> []; x : xs' -> f x : map f xs' }"
               ]
          $  "Section section_map_0. "
          ++ "(* Constant arguments for map *) "
          ++ "Variable Shape : Type. "
          ++ "Variable Pos : Shape -> Type. "
          ++ "Variable a_0 b_0 : Type. "
          ++ "Variable f_0 : Free Shape Pos"
          ++ "  (Free Shape Pos a_0 -> Free Shape Pos b_0). "
          ++ "(* Helper functions for map *) "
          ++ "Fixpoint map_1 (xs : List Shape Pos a_0) {struct xs}"
          ++ " : Free Shape Pos (List Shape Pos b_0)"
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
        it
            "creates variable sentences for type variables in constant argument types"
          $  shouldSucceed
          $  fromConverter
          $  shouldTranslateDeclsTo
               [ "mapAlt :: (a -> b) -> [a] -> [b]"
               , "mapAlt f xs = case xs of {"
               ++ "  []      -> [];"
               ++ "  x : xs' -> f x : mapAlt' f xs'"
               ++ "}"
               , "mapAlt' :: (b -> a) -> [b] -> [a]"
               , "mapAlt' f xs = case xs of {"
               ++ "  []      -> [];"
               ++ "  x : xs' -> f x : mapAlt f xs'"
               ++ "}"
               ]
          $  "Section section_mapAlt_mapAlt'_0. "
          ++ "(* Constant arguments for mapAlt, mapAlt' *) "
          ++ "Variable Shape : Type. "
          ++ "Variable Pos : Shape -> Type. "
          ++ "Variable a_0 b_0 : Type. "
          ++ "Variable f_0 : Free Shape Pos"
          ++ "  (Free Shape Pos a_0 -> Free Shape Pos b_0). "
          ++ "(* Helper functions for mapAlt, mapAlt' *) "
          ++ "Fixpoint mapAlt_1 (xs : List Shape Pos a_0) {struct xs}"
          ++ " : Free Shape Pos (List Shape Pos b_0)"
          ++ "  := match xs with"
          ++ "     | nil            => @Nil Shape Pos b_0"
          ++ "     | cons x xs' =>"
          ++ "        @Cons Shape Pos b_0"
          ++ "          (f_0 >>= (fun f_1 => f_1 x))"
          ++ "          (xs' >>= (fun (xs'_0 : List Shape Pos a_0) =>"
          ++ "             mapAlt'_1 xs'_0))"
          ++ "     end"
          ++ " with mapAlt'_1 (xs : List Shape Pos a_0) {struct xs}"
          ++ " : Free Shape Pos (List Shape Pos b_0)"
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
        it "does not create variable sentences for unsued constant arguments"
          $  shouldSucceed
          $  fromConverter
          $  shouldTranslateDeclsTo
               [ "foo :: a -> a -> [a] -> [a]"
               , "foo u v xs = case xs of { [] -> []; x : xs' -> v : foo u v xs' }"
               ]
          $  "Section section_foo_0. "
          ++ "(* Constant arguments for foo *) "
          ++ "Variable Shape : Type. "
          ++ "Variable Pos : Shape -> Type. "
          ++ "Variable a_0 : Type. "
          ++ "Variable v_0 : Free Shape Pos a_0. "
          ++ "(* Helper functions for foo *) "
          ++ "Fixpoint foo_1 (xs : List Shape Pos a_0) {struct xs}"
          ++ " : Free Shape Pos (List Shape Pos a_0)"
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
          $  shouldSucceed
          $  fromConverter
          $  shouldTranslateDeclsTo
               [ "foo :: a -> b -> [c] -> [b]"
               , "foo u v xs = case xs of { [] -> []; x : xs' -> v : foo u v xs' }"
               ]
          $  "Section section_foo_0. "
          ++ "(* Constant arguments for foo *) "
          ++ "Variable Shape : Type. "
          ++ "Variable Pos : Shape -> Type. "
          ++ "Variable b_0 : Type. "
          ++ "Variable v_0 : Free Shape Pos b_0. "
          ++ "(* Helper functions for foo *) "
          ++ "Fixpoint foo_1 {a_0 c_0 : Type}"
          ++ "  (xs : List Shape Pos c_0) {struct xs}"
          ++ " : Free Shape Pos (List Shape Pos b_0)"
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
