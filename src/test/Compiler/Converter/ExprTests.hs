module Compiler.Converter.ExprTests where

import           Test.Hspec

import           Compiler.Util.Test

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Test group for 'convertExpr' tests.
testConvertExpr :: Spec
testConvertExpr = describe "Compiler.Converter.Expr.convertExpr" $ do
  testConvertUnknownIdents
  testConvertConApp
  testConvertFuncApp
  testConvertInfix
  testConvertIf
  testConvertCase
  testConvertLambda
  testConvertExprTypeSigs
  testConvertInteger
  testConvertBool
  testConvertLists
  testConvertTuples

-------------------------------------------------------------------------------
-- Identifiers                                                               --
-------------------------------------------------------------------------------

-- | Test group for error reporting during conversion of expressions.
testConvertUnknownIdents :: Spec
testConvertUnknownIdents = context "unknown identifiers are reported" $ do
  it "fails to translate unknown constructors"
    $ shouldReportFatal
    $ fromConverter
    $ convertTestExpr "C"

  it "fails to translate unknown variables or functions"
    $ shouldReportFatal
    $ fromConverter
    $ convertTestExpr "x"

-------------------------------------------------------------------------------
-- Constructor applications                                                  --
-------------------------------------------------------------------------------

-- | Test group for translation of constructor application expressions.
testConvertConApp :: Spec
testConvertConApp = context "constructor applications" $ do
  it "converts 0-ary constructor applications correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "D"        <- defineTestTypeCon "D" 0
        ("c", "C") <- defineTestCon "C" 0 "D"
        "C" `shouldTranslateExprTo` "C Shape Pos"

  it "converts complete constructor applications correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "D"        <- defineTestTypeCon "D" 0
        ("c", "C") <- defineTestCon "C" 3 "a -> b -> c -> D"
        "x"        <- defineTestVar "x"
        "y"        <- defineTestVar "y"
        "z"        <- defineTestVar "z"
        "C x y z" `shouldTranslateExprTo` "C Shape Pos x y z"

  it "converts partial constructor applications correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "D"        <- defineTestTypeCon "D" 0
        ("c", "C") <- defineTestCon "C" 3 "a -> b -> c -> D"
        "x"        <- defineTestVar "x"
        "y"        <- defineTestVar "y"
        shouldTranslateExprTo "C x y" $ "pure (fun x_0 => C Shape Pos x y x_0)"

  it "converts multiply partial constructor applications correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "D"        <- defineTestTypeCon "D" 0
        ("c", "C") <- defineTestCon "C" 3 "a -> b -> c -> D"
        "x"        <- defineTestVar "x"
        shouldTranslateExprTo "C x"
          $ "pure (fun x_0 => pure (fun x_1 => C Shape Pos x x_0 x_1))"

  it "converts unapplied constructors correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "D"        <- defineTestTypeCon "D" 0
        ("c", "C") <- defineTestCon "C" 3 "a -> b -> c -> D"
        shouldTranslateExprTo "C"
          $  "pure (fun x_0 => pure (fun x_1 => pure (fun x_2 =>"
          ++ "  C Shape Pos x_0 x_1 x_2"
          ++ ")))"

  it "converts infix constructor applications correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "x"  <- defineTestVar "x"
        "xs" <- defineTestVar "xs"
        "t0" <- defineTestTypeVar "t0"
        "x : xs" `shouldTranslateExprTo` "@Cons Shape Pos t0 x xs"

-------------------------------------------------------------------------------
-- Function applications                                                     --
-------------------------------------------------------------------------------

-- | Test group for translation of function application expressions.
testConvertFuncApp :: Spec
testConvertFuncApp = context "function applications" $ do
  it "converts 0-ary function (pattern-binding) applications correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "f"  <- defineTestFunc "f" 0 "a"
        "t0" <- defineTestTypeVar "t0"
        "f" `shouldTranslateExprTo` "@f Shape Pos t0"

  it "converts complete function applications correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "f"  <- defineTestFunc "f" 3 "a -> b -> c -> d"
        "x"  <- defineTestVar "x" -- :: t1
        "y"  <- defineTestVar "y" -- :: t2
        "z"  <- defineTestVar "z" -- :: t3
        "t0" <- defineTestTypeVar "t0"
        "t1" <- defineTestTypeVar "t1"
        "t2" <- defineTestTypeVar "t2"
        "t3" <- defineTestTypeVar "t3"
        "f x y z" `shouldTranslateExprTo` "@f Shape Pos t1 t2 t3 t0 x y z"

  it "converts partial function applications correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "f"  <- defineTestFunc "f" 3 "a -> b -> c -> d"
        "x"  <- defineTestVar "x" -- :: t2
        "y"  <- defineTestVar "y" -- :: t3
        "t0" <- defineTestTypeVar "t0"
        "t1" <- defineTestTypeVar "t1"
        "t2" <- defineTestTypeVar "t2"
        "t3" <- defineTestTypeVar "t3"
        shouldTranslateExprTo "f x y"
          $ "pure (fun x_0 => @f Shape Pos t2 t3 t0 t1 x y x_0)"

  it "converts multiply partial function applications correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "f"  <- defineTestFunc "f" 3 "a -> b -> c -> d"
        "x"  <- defineTestVar "x" -- :: t3
        "t0" <- defineTestTypeVar "t0"
        "t1" <- defineTestTypeVar "t1"
        "t2" <- defineTestTypeVar "t2"
        "t3" <- defineTestTypeVar "t3"
        shouldTranslateExprTo "f x"
          $  "pure (fun x_0 => pure (fun x_1 =>"
          ++ "  @f Shape Pos t3 t0 t1 t2 x x_0 x_1))"

  it "converts unapplied functions correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "f"  <- defineTestFunc "f" 3 "a -> b -> c -> d"
        "t0" <- defineTestTypeVar "t0"
        "t1" <- defineTestTypeVar "t1"
        "t2" <- defineTestTypeVar "t2"
        "t3" <- defineTestTypeVar "t3"
        shouldTranslateExprTo "f"
          $  "pure (fun x_0 => pure (fun x_1 => pure (fun x_2 =>"
          ++ "  @f Shape Pos t0 t1 t2 t3 x_0 x_1 x_2"
          ++ ")))"

  it "converts applications of partial functions correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "f"  <- definePartialTestFunc "f" 1 "a -> b -> c"
        "x"  <- defineTestVar "x" -- :: t2
        "t0" <- defineTestTypeVar "t0"
        "t1" <- defineTestTypeVar "t1"
        "t2" <- defineTestTypeVar "t2"
        "f x" `shouldTranslateExprTo` "@f Shape Pos P t2 t0 t1 x"

  it "converts applications of functions correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "e1" <- defineTestVar "e1"
        "e2" <- defineTestVar "e2"
        "e1 e2" `shouldTranslateExprTo` "e1 >>= (fun e1_0 => e1_0 e2)"

  it "converts applications of functions that return functions correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "f"  <- defineTestFunc "f" 1 "a -> b -> c"
        "x"  <- defineTestVar "x" -- :: t1
        "y"  <- defineTestVar "y" -- :: t2
        "t0" <- defineTestTypeVar "t0"
        "t1" <- defineTestTypeVar "t1"
        "t2" <- defineTestTypeVar "t2"
        shouldTranslateExprTo "f x y"
                              "@f Shape Pos t1 t2 t0 x >>= (fun f_0 => f_0 y)"

-------------------------------------------------------------------------------
-- Infix expressions                                                         --
-------------------------------------------------------------------------------

-- | Test group for translation of infix expressions.
testConvertInfix :: Spec
testConvertInfix = context "infix expressions" $ do
  it "converts infix expressions correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "f"  <- defineTestFunc "f" 2 "a -> b -> c"
        "e1" <- defineTestVar "e1" -- :: t1
        "e2" <- defineTestVar "e2" -- :: t2
        "t0" <- defineTestTypeVar "t0"
        "t1" <- defineTestTypeVar "t1"
        "t2" <- defineTestTypeVar "t2"
        "e1 `f` e2" `shouldTranslateExprTo` "@f Shape Pos t1 t2 t0 e1 e2"

  it "converts left sections correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "f"  <- defineTestFunc "f" 2 "a -> b -> c"
        "e1" <- defineTestVar "e1" -- :: t2
        "t0" <- defineTestTypeVar "t0"
        "t1" <- defineTestTypeVar "t1"
        "t2" <- defineTestTypeVar "t2"
        shouldTranslateExprTo "(e1 `f`)"
                              "pure (fun x_0 => @f Shape Pos t2 t0 t1 e1 x_0)"

  it "converts right sections correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "f"  <- defineTestFunc "f" 2 "a -> b -> c"
        "e2" <- defineTestVar "e2" -- :: t2
        "t0" <- defineTestTypeVar "t0"
        "t1" <- defineTestTypeVar "t1"
        "t2" <- defineTestTypeVar "t2"
        shouldTranslateExprTo
          "(`f` e2)"
          "pure (fun (x_0 : Free Shape Pos t0) => @f Shape Pos t0 t2 t1 x_0 e2)"

-------------------------------------------------------------------------------
-- If-expressions                                                            --
-------------------------------------------------------------------------------

-- | Test group for translation of @if@-expressions.
testConvertIf :: Spec
testConvertIf = context "if expressions" $ do
  it "converts if expressions correctly" $ shouldSucceed $ fromConverter $ do
    "e1" <- defineTestVar "e1"
    "e2" <- defineTestVar "e2"
    "e3" <- defineTestVar "e3"
    shouldTranslateExprTo "if e1 then e2 else e3"
      $ "e1 >>= (fun (e1_0 : Bool Shape Pos) => if e1_0 then e2 else e3)"

  it "there is no name conflict with custom `Bool`"
    $ shouldSucceed
    $ fromConverter
    $ do
        "Bool0" <- defineTestTypeCon "Bool" 0
        "e1"    <- defineTestVar "e1"
        "e2"    <- defineTestVar "e2"
        "e3"    <- defineTestVar "e3"
        shouldTranslateExprTo "if e1 then e2 else e3"
          $ "e1 >>= (fun (e1_0 : Bool Shape Pos) => if e1_0 then e2 else e3)"

-------------------------------------------------------------------------------
-- Case-expressions                                                          --
-------------------------------------------------------------------------------

-- | Test group for translation of @case@-expressions.
testConvertCase :: Spec
testConvertCase = context "case expressions" $ do
  it "simplifies matches with only one alternative (during pretty printing)"
    $ shouldSucceed
    $ fromConverter
    $ do
        "e"        <- defineTestVar "e"
        "e'"       <- defineTestVar "e'"
        "D"        <- defineTestTypeCon "D" 0
        ("c", "C") <- defineTestCon "C" 0 "D"
        "case e of { C -> e' }" `shouldTranslateExprTo` "e >>= (fun '(c) => e')"

  it "uses data (not smart) constructors" $ shouldSucceed $ fromConverter $ do
    "e"          <- defineTestVar "e"
    "e1"         <- defineTestVar "e1"
    "e2"         <- defineTestVar "e2"
    "D"          <- defineTestTypeCon "D" 0
    ("c1", "C1") <- defineTestCon "C1" 0 "D"
    ("c2", "C2") <- defineTestCon "C2" 0 "D"
    shouldTranslateExprTo "case e of { C1 -> e1;  C2 -> e2 }"
      $  "e >>= (fun e_0 =>"
      ++ "  match e_0 with"
      ++ "  | c1 => e1"
      ++ "  | c2 => e2"
      ++ "  end)"

  it "can convert matches of list constructors"
    $ shouldSucceed
    $ fromConverter
    $ do
        "xs" <- defineTestVar "xs"
        "t0" <- defineTestTypeVar "t0"
        shouldTranslateExprTo "case xs of { [] -> undefined; y : ys -> y }"
          $  "xs >>= (fun xs_0 =>"
          ++ "  match xs_0 with"
          ++ "  | nil => @undefined Shape Pos P t0"
          ++ "  | cons y ys => y"
          ++ "  end)"

  it "allows case expressions to shadow local variables"
    $ shouldSucceed
    $ fromConverter
    $ do
        "e" <- defineTestVar "e"
        "x" <- defineTestVar "x"
        shouldTranslateExprTo "case e of { [] -> x; x : xs -> x }"
          $  "e >>= (fun e_0 =>"
          ++ "  match e_0 with"
          ++ "  | nil => x"
          ++ "  | cons x0 xs => x0"
          ++ "  end)"

-------------------------------------------------------------------------------
-- Lambda abstractions                                                       --
-------------------------------------------------------------------------------

-- | Test group for translation of lambda abstractions.
testConvertLambda :: Spec
testConvertLambda = context "lambda abstractions" $ do
  it "translates single argument lambda abstractions correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "t0" <- defineTestTypeVar "t0"
        "e"  <- defineTestVar "e"
        shouldTranslateExprTo "\\x -> e"
                              "pure (fun (x : Free Shape Pos t0) => e)"

  it "translates multi argument lambda abstractions correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "t0" <- defineTestTypeVar "t0"
        "t1" <- defineTestTypeVar "t1"
        "e"  <- defineTestVar "e"
        shouldTranslateExprTo "\\x y -> e"
          $  "pure (fun (x : Free Shape Pos t0) =>"
          ++ "  pure (fun (y : Free Shape Pos t1) => e))"

  it "allows lambda abstractions to shadow local variables"
    $ shouldSucceed
    $ fromConverter
    $ do
        "t0" <- defineTestTypeVar "t0"
        "x"  <- defineTestVar "x"
        shouldTranslateExprTo "\\x -> x"
                              "pure (fun (x0 : Free Shape Pos t0) => x0)"

-------------------------------------------------------------------------------
-- Type signatures                                                           --
-------------------------------------------------------------------------------

-- | Test group for translation of expressions with type signatures.
testConvertExprTypeSigs :: Spec
testConvertExprTypeSigs = context "type signatures" $ do
  it "translates expressions with type signatures correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "42 :: Integer" `shouldTranslateExprTo` "pure 42%Z"
  it "type signatures make type arguments more specific"
    $ shouldSucceed
    $ fromConverter
    $ do
        shouldTranslateExprTo "[] :: [Integer]"
                              "@Nil Shape Pos (Integer Shape Pos)"

-------------------------------------------------------------------------------
-- Integer expressions                                                       --
-------------------------------------------------------------------------------

-- | Test group for translation of integer expressions.
testConvertInteger :: Spec
testConvertInteger = context "integer expressions" $ do
  it "translates zero correctly"
    $ shouldSucceed
    $ fromConverter
    $ shouldTranslateExprTo "0" "pure 0%Z"

  it "translates positive decimal integer literals correctly"
    $ shouldSucceed
    $ fromConverter
    $ shouldTranslateExprTo "42" "pure 42%Z"

  it "translates hexadecimal integer literals correctly"
    $ shouldSucceed
    $ fromConverter
    $ shouldTranslateExprTo "0xA2" "pure 162%Z"

  it "translates octal integer literals correctly"
    $ shouldSucceed
    $ fromConverter
    $ shouldTranslateExprTo "0o755" "pure 493%Z"

  it "translates negative decimal integer literals correctly"
    $ shouldSucceed
    $ fromConverter
    $ shouldTranslateExprTo "-42" "negate Shape Pos (pure 42%Z)"

  it "cannot shadow negate" $ shouldSucceed $ fromConverter $ do
    "negate0" <- defineTestFunc "negate" 1 "Integer -> Integer"
    shouldTranslateExprTo "-42" "negate Shape Pos (pure 42%Z)"

  it "translates arithmetic expressions correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "a" <- defineTestVar "a"
        "b" <- defineTestVar "b"
        "c" <- defineTestVar "c"
        "x" <- defineTestVar "x"
        shouldTranslateExprTo "a * x^2 + b * x + c"
          $  "addInteger Shape Pos"
          ++ "  (addInteger Shape Pos"
          ++ "    (mulInteger Shape Pos a (powInteger Shape Pos x (pure 2%Z)))"
          ++ "    (mulInteger Shape Pos b x))"
          ++ "  c"

-------------------------------------------------------------------------------
-- Boolean expressions                                                       --
-------------------------------------------------------------------------------

-- | Test group for translation of boolean expressions.
testConvertBool :: Spec
testConvertBool = context "boolean expressions" $ do
  it "translates 'True' correctly" $ shouldSucceed $ fromConverter $ do
    "True" `shouldTranslateExprTo` "True_ Shape Pos"

  it "translates 'False' correctly" $ shouldSucceed $ fromConverter $ do
    "False" `shouldTranslateExprTo` "False_ Shape Pos"

  it "translates conjunction correctly" $ shouldSucceed $ fromConverter $ do
    "x" <- defineTestVar "x"
    "y" <- defineTestVar "y"
    "x && y" `shouldTranslateExprTo` "andBool Shape Pos x y"

  it "translates disjunction correctly" $ shouldSucceed $ fromConverter $ do
    "x" <- defineTestVar "x"
    "y" <- defineTestVar "y"
    "x || y" `shouldTranslateExprTo` "orBool Shape Pos x y"

-------------------------------------------------------------------------------
-- Lists                                                                     --
-------------------------------------------------------------------------------

-- | Test group for translation of list expressions.
testConvertLists :: Spec
testConvertLists = context "list expressions" $ do
  it "translates empty list constructor correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "t0" <- defineTestTypeVar "t0"
        shouldTranslateExprTo "[]" "@Nil Shape Pos t0"

  it "translates non-empty list constructor correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "x"  <- defineTestVar "x"
        "xs" <- defineTestVar "xs"
        "t0" <- defineTestTypeVar "t0"
        "x : xs" `shouldTranslateExprTo` "@Cons Shape Pos t0 x xs"

  it "translates list literal correctly" $ shouldSucceed $ fromConverter $ do
    "x1" <- defineTestVar "x1"
    "x2" <- defineTestVar "x2"
    "x3" <- defineTestVar "x3"
    "t0" <- defineTestTypeVar "t0"
    shouldTranslateExprTo "[x1, x2, x3]"
      $  "@Cons Shape Pos t0 x1 ("
      ++ "@Cons Shape Pos t0 x2 ("
      ++ "@Cons Shape Pos t0 x3 ("
      ++ "@Nil Shape Pos t0)))"

-------------------------------------------------------------------------------
-- Tuples                                                                    --
-------------------------------------------------------------------------------

-- | Test group for translation of tuple expressions.
testConvertTuples :: Spec
testConvertTuples = context "tuple expressions" $ do
  it "translates unit literals correctly" $ shouldSucceed $ fromConverter $ do
    "()" `shouldTranslateExprTo` "Tt Shape Pos"

  it "translates pair literals correctly" $ shouldSucceed $ fromConverter $ do
    "x"  <- defineTestVar "x"
    "y"  <- defineTestVar "y"
    "t0" <- defineTestTypeVar "t0"
    "t1" <- defineTestTypeVar "t1"
    "(x, y)" `shouldTranslateExprTo` "@Pair_ Shape Pos t0 t1 x y"

  it "translates pair constructor correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "x"  <- defineTestVar "x"
        "y"  <- defineTestVar "y"
        "t0" <- defineTestTypeVar "t0"
        "t1" <- defineTestTypeVar "t1"
        "(,) x y" `shouldTranslateExprTo` "@Pair_ Shape Pos t0 t1 x y"
