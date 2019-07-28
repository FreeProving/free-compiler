module Compiler.ConverterTests where

import           Test.Hspec

import           Compiler.Converter.Renamer
import           Compiler.Converter.State
import           Compiler.Language.Haskell.SimpleAST
                                               as HS

import           Compiler.Util.Test

-- | Test group for all @Compiler.Converter@ tests.
testConverter :: Spec
testConverter = describe "Compiler.Converter" $ do
  testConvertType
  testConvertDataDecls
  testConvertExpr
  testConvertNonRecFuncDecl
  testConvertRecFuncDecls

-------------------------------------------------------------------------------
-- Data type declarations                                                    --
-------------------------------------------------------------------------------

-- | Test group for 'convertDataDecls' tests.
testConvertDataDecls :: Spec
testConvertDataDecls = describe "convertDataDecls" $ do
  it "translates non-polymorphic types correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        shouldTranslateDeclsTo ["data Foo = Bar | Baz"]
          $  "Inductive Foo (Shape : Type) (Pos : Shape -> Type) : Type "
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

  it "translates polymorphic types correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        shouldTranslateDeclsTo ["data Foo a b = Bar a | Baz b"]
          $  "Inductive Foo (Shape : Type) (Pos : Shape -> Type) "
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
          $  "Inductive Foo (Shape : Type) (Pos : Shape -> Type) : Type "
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
          $  "Inductive Foo (Shape : Type) (Pos : Shape -> Type) "
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
          $  "Inductive Bar (Shape : Type) (Pos : Shape -> Type) : Type"
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

-------------------------------------------------------------------------------
-- Non-recursive function declarations                                       --
-------------------------------------------------------------------------------

-- | Test group for 'convertNonRecFuncDecl' tests.
testConvertNonRecFuncDecl :: Spec
testConvertNonRecFuncDecl = describe "convertNonRecursiveFunction" $ do
  it "translates 0-ary functions (pattern-bindings) correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        shouldTranslateDeclsTo ["foo :: Int", "foo = 42"]
          $  "Definition foo (Shape : Type) (Pos : Shape -> Type)"
          ++ "  : Free Shape Pos (Int Shape Pos)"
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
          $  "Definition foo (Shape : Type) (Pos : Shape -> Type) {a b : Type}"
          ++ "  (x : Free Shape Pos a) (y : Free Shape Pos b)"
          ++ "  : Free Shape Pos (Pair Shape Pos a b)"
          ++ "  := Pair_ Shape Pos x y."

  it "translates higher order functions correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        shouldTranslateDeclsTo
            ["curry :: ((a, b) -> c) -> a -> b -> c", "curry f x y = f (x, y)"]
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
testConvertRecFuncDecls = describe "convertRecFuncDecls" $ do
  it "requires a case expression"
    $ shouldReportFatal
    $ fromConverter
    $ convertTestDecls ["loop :: a", "loop = loop"]

  it "requires a case expression for a variable"
    $ shouldReportFatal
    $ fromConverter
    $ convertTestDecls ["loop :: a", "loop = case () of () -> loop"]

  it "requires a case expression for an argument"
    $ shouldReportFatal
    $ fromConverter
    $ do
        "x" <- renameAndDefineFunc "x" 0
        convertTestDecls ["loop :: a", "loop = case x of () -> loop"]

  -- TODO detect whether the function is actually decreasing on it's
  --      decreasing argument.
  -- it "requires a decreasing argument"
  --   $ shouldReportFatal
  --   $ fromConverter
  --   $ do
  --       convertTestDecls ["loop :: a -> a", "loop x = case x of () -> loop x"]

  it "translates simple recursive functions correctly"
    $  shouldSucceed
    $  fromConverter
    $  shouldTranslateDeclsTo
         [ "length :: [a] -> Int"
         , "length xs = case xs of { [] -> 0; x : xs' -> length xs' + 1 }"
         ]
    $  "Fixpoint length_0 (Shape : Type) (Pos : Shape -> Type) {a : Type}"
    ++ "  (xs : List Shape Pos a)"
    ++ "  {struct xs}"
    ++ "  : Free Shape Pos (Int Shape Pos)"
    ++ "  := match xs with"
    ++ "     | nil        => pure 0%Z"
    ++ "     | cons x xs' => addInt Shape Pos"
    ++ "         (xs' >>= (fun xs'_0 => length_0 Shape Pos xs'_0))"
    ++ "         (pure 1%Z)"
    ++ "     end. "
    ++ "Definition length (Shape : Type) (Pos : Shape -> Type) {a : Type}"
    ++ "  (xs : Free Shape Pos (List Shape Pos a))"
    ++ "  : Free Shape Pos (Int Shape Pos)"
    ++ "  := xs >>= (fun xs_0 => length_0 Shape Pos xs_0)."

  it "lifts uses of the decreasing argument"
    $ shouldSucceed
    $ fromConverter
    $ shouldTranslateDeclsTo
          ["tails :: [a] -> [[a]]"
          , "tails xs = case xs of { [] -> []; x : xs' -> xs : tails xs' }"]
    $ "Fixpoint tails_0 (Shape : Type) (Pos : Shape -> Type) {a : Type}"
    ++ "  (xs : List Shape Pos a)"
    ++ "  {struct xs}"
    ++ "  : Free Shape Pos (List Shape Pos (List Shape Pos a))"
    ++ "  := match xs with"
    ++ "     | nil => Nil Shape Pos"
    ++ "     | cons x xs' => Cons Shape Pos"
    ++ "         (pure xs)"
    ++ "         (xs' >>= (fun xs'_0 => tails_0 Shape Pos xs'_0))"
    ++ "     end. "
    ++ " Definition tails (Shape : Type) (Pos : Shape -> Type) {a : Type}"
    ++ "   (xs : Free Shape Pos (List Shape Pos a))"
    ++ "   : Free Shape Pos (List Shape Pos (List Shape Pos a))"
    ++ "   := xs >>= (fun xs_0 => tails_0 Shape Pos xs_0)."

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------

-- | Test group for 'convertType' tests.
testConvertType :: Spec
testConvertType = describe "convertType" $ do
  it "fails to translate unknown type varaibles"
    $ shouldReportFatal
    $ fromConverter
    $ convertTestType "a"

  it "fails to translate unknown type constructor"
    $ shouldReportFatal
    $ fromConverter
    $ convertTestType "NoSuchType"

  it "translates 'a' correctly" $ shouldSucceed $ fromConverter $ do
    "a" <- renameAndDefineTypeVar "a"
    "a" `shouldTranslateTypeTo` "Free Shape Pos a"

  it "translates 'Bool' correctly" $ shouldSucceed $ fromConverter $ do
    "Bool" `shouldTranslateTypeTo` "Free Shape Pos (Bool Shape Pos)"

  it "translates 'Int' correctly" $ shouldSucceed $ fromConverter $ do
    "Int" `shouldTranslateTypeTo` "Free Shape Pos (Int Shape Pos)"

  it "translates custom types correctly" $ shouldSucceed $ fromConverter $ do
    "Foo" <- renameAndDefineTypeCon "Foo" 0
    "Foo" `shouldTranslateTypeTo` "Free Shape Pos (Foo Shape Pos)"

  it "translates '()' correctly" $ shouldSucceed $ fromConverter $ do
    "()" `shouldTranslateTypeTo` "Free Shape Pos (Unit Shape Pos)"

  it "translates '[a]' correctly" $ shouldSucceed $ fromConverter $ do
    "a" <- renameAndDefineTypeVar "a"
    "[a]" `shouldTranslateTypeTo` "Free Shape Pos (List Shape Pos a)"

  it "translates '(a, b)' correctly" $ shouldSucceed $ fromConverter $ do
    "a" <- renameAndDefineTypeVar "a"
    "b" <- renameAndDefineTypeVar "b"
    "(a, b)" `shouldTranslateTypeTo` "Free Shape Pos (Pair Shape Pos a b)"

  it "translates 'a -> b' correctly" $ shouldSucceed $ fromConverter $ do
    "a" <- renameAndDefineTypeVar "a"
    "b" <- renameAndDefineTypeVar "b"
    shouldTranslateTypeTo
      "a -> b"
      "Free Shape Pos (Free Shape Pos a -> Free Shape Pos b)"

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Test group for 'convertExpr' tests.
testConvertExpr :: Spec
testConvertExpr = describe "convertExpr" $ do
  testConvertUnknownIdents
  testConvertConApp
  testConvertFuncApp
  testConvertInfix
  testConvertIf
  testConvertCase
  testConvertLambda
  testConvertInt
  testConvertBool
  testConvertLists
  testConvertTuples

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

-- | Test group for translation of constructor application expressions.
testConvertConApp :: Spec
testConvertConApp = context "constructor applications" $ do
  it "converts 0-ary constructor applications correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        ("c", "C") <- renameAndDefineCon "C" 0
        "C" `shouldTranslateExprTo` "C Shape Pos"

  it "converts complete constructor applications correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        ("c", "C") <- renameAndDefineCon "C" 3
        "x"        <- renameAndDefineVar "x"
        "y"        <- renameAndDefineVar "y"
        "z"        <- renameAndDefineVar "z"
        "C x y z" `shouldTranslateExprTo` "C Shape Pos x y z"

  it "converts partial constructor applications correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        ("c", "C") <- renameAndDefineCon "C" 3
        "x"        <- renameAndDefineVar "x"
        "y"        <- renameAndDefineVar "y"
        shouldTranslateExprTo "C x y" $ "pure (fun x_0 => C Shape Pos x y x_0)"

  it "converts multiply partial constructor applications correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        ("c", "C") <- renameAndDefineCon "C" 3
        "x"        <- renameAndDefineVar "x"
        shouldTranslateExprTo "C x"
          $ "pure (fun x_0 => pure (fun x_1 => C Shape Pos x x_0 x_1))"

  it "converts unapplied constructors correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        ("c", "C") <- renameAndDefineCon "C" 3
        shouldTranslateExprTo "C"
          $  "pure (fun x_0 => pure (fun x_1 => pure (fun x_2 =>"
          ++ "  C Shape Pos x_0 x_1 x_2"
          ++ ")))"

  it "converts infix constructor applications correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "x"  <- renameAndDefineVar "x"
        "xs" <- renameAndDefineVar "xs"
        "x : xs" `shouldTranslateExprTo` "Cons Shape Pos x xs"

-- | Test group for translation of function application expressions.
testConvertFuncApp :: Spec
testConvertFuncApp = context "function applications" $ do
  it "converts 0-ary function (pattern-binding) applications correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "f" <- renameAndDefineFunc "f" 0
        "f" `shouldTranslateExprTo` "f Shape Pos"

  it "converts complete function applications correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "f" <- renameAndDefineFunc "f" 3
        "x" <- renameAndDefineVar "x"
        "y" <- renameAndDefineVar "y"
        "z" <- renameAndDefineVar "z"
        "f x y z" `shouldTranslateExprTo` "f Shape Pos x y z"

  it "converts partial function applications correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "f" <- renameAndDefineFunc "f" 3
        "x" <- renameAndDefineVar "x"
        "y" <- renameAndDefineVar "y"
        shouldTranslateExprTo "f x y" $ "pure (fun x_0 => f Shape Pos x y x_0)"

  it "converts multiply partial function applications correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "f" <- renameAndDefineFunc "f" 3
        "x" <- renameAndDefineVar "x"
        shouldTranslateExprTo "f x"
          $ "pure (fun x_0 => pure (fun x_1 => f Shape Pos x x_0 x_1))"

  it "converts unapplied functions correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "f" <- renameAndDefineFunc "f" 3
        shouldTranslateExprTo "f"
          $  "pure (fun x_0 => pure (fun x_1 => pure (fun x_2 =>"
          ++ "  f Shape Pos x_0 x_1 x_2"
          ++ ")))"

  it "converts applications of partial functions correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "f" <- renameAndDefineFunc "f" 1
        modifyEnv $ definePartial (HS.Ident "f")
        "x" <- renameAndDefineVar "x"
        "f x" `shouldTranslateExprTo` "f Shape Pos P x"

  it "converts applications of functions correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "e1" <- renameAndDefineVar "e1"
        "e2" <- renameAndDefineVar "e2"
        "e1 e2" `shouldTranslateExprTo` "e1 >>= (fun e1_0 => e1_0 e2)"

  it "converts applications of functions that return functions correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "f" <- renameAndDefineFunc "f" 1
        "x" <- renameAndDefineVar "x"
        "y" <- renameAndDefineVar "y"
        "f x y" `shouldTranslateExprTo` "f Shape Pos x >>= (fun x_0 => x_0 y)"

-- | Test group for translation of infix expressions.
testConvertInfix :: Spec
testConvertInfix = context "infix expressions" $ do
  it "converts infix expressions correctly" $ shouldSucceed $ fromConverter $ do
    "f"  <- renameAndDefineFunc "f" 2
    "e1" <- renameAndDefineVar "e1"
    "e2" <- renameAndDefineVar "e2"
    "e1 `f` e2" `shouldTranslateExprTo` "f Shape Pos e1 e2"

  it "converts left sections correctly" $ shouldSucceed $ fromConverter $ do
    "f"  <- renameAndDefineFunc "f" 2
    "e1" <- renameAndDefineVar "e1"
    "(e1 `f`)" `shouldTranslateExprTo` "pure (fun x_0 => f Shape Pos e1 x_0)"

  it "converts right sections correctly" $ shouldSucceed $ fromConverter $ do
    "f"  <- renameAndDefineFunc "f" 2
    "e2" <- renameAndDefineVar "e2"
    "(`f` e2)" `shouldTranslateExprTo` "pure (fun x_0 => f Shape Pos x_0 e2)"

-- | Test group for translation of @if@-expressions.
testConvertIf :: Spec
testConvertIf = context "if expressions" $ do
  it "converts if expressions correctly" $ shouldSucceed $ fromConverter $ do
    "e1" <- renameAndDefineVar "e1"
    "e2" <- renameAndDefineVar "e2"
    "e3" <- renameAndDefineVar "e3"
    shouldTranslateExprTo "if e1 then e2 else e3"
      $ "e1 >>= (fun (e1_0 : Bool Shape Pos) => if e1_0 then e2 else e3)"

  it "there is no name conflict with custom `Bool`"
    $ shouldSucceed
    $ fromConverter
    $ do
        "Bool0" <- renameAndDefineTypeCon "Bool" 0
        "e1"    <- renameAndDefineVar "e1"
        "e2"    <- renameAndDefineVar "e2"
        "e3"    <- renameAndDefineVar "e3"
        shouldTranslateExprTo "if e1 then e2 else e3"
          $ "e1 >>= (fun (e1_0 : Bool Shape Pos) => if e1_0 then e2 else e3)"

-- | Test group for translation of @case@-expressions.
testConvertCase :: Spec
testConvertCase = context "case expressions" $ do
  it "simplifies matches with only one alternative (during pretty printing)"
    $ shouldSucceed
    $ fromConverter
    $ do
        "e"        <- renameAndDefineVar "e"
        "e'"       <- renameAndDefineVar "e'"
        ("c", "C") <- renameAndDefineCon "C" 0
        "case e of { C -> e' }" `shouldTranslateExprTo` "e >>= (fun '(c) => e')"

  it "uses data (not smart) constructors" $ shouldSucceed $ fromConverter $ do
    "e"          <- renameAndDefineVar "e"
    "e1"         <- renameAndDefineVar "e1"
    "e2"         <- renameAndDefineVar "e2"
    ("c1", "C1") <- renameAndDefineCon "C1" 0
    ("c2", "C2") <- renameAndDefineCon "C2" 0
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
        "xs" <- renameAndDefineVar "xs"
        shouldTranslateExprTo "case xs of { [] -> undefined; y : ys -> y }"
          $  "xs >>= (fun xs_0 =>"
          ++ "  match xs_0 with"
          ++ "  | nil => undefined"
          ++ "  | cons y ys => y"
          ++ "  end)"

-- | Test group for translation of lambda abstractions.
testConvertLambda :: Spec
testConvertLambda = context "lambda abstractions" $ do
  it "translates single argument lambda abstractions correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "e" <- renameAndDefineVar "e"
        "\\x -> e" `shouldTranslateExprTo` "pure (fun x => e)"

  it "translates multi argument lambda abstractions correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "e" <- renameAndDefineVar "e"
        shouldTranslateExprTo "\\x y -> e" "pure (fun x => pure (fun y => e))"

-- | Test group for translation of integer expressions.
testConvertInt :: Spec
testConvertInt = context "integer expressions" $ do
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
    "negate0" <- renameAndDefineFunc "negate" 1
    shouldTranslateExprTo "-42" "negate Shape Pos (pure 42%Z)"

  it "translates arithmetic expressions correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "a" <- renameAndDefineVar "a"
        "b" <- renameAndDefineVar "b"
        "c" <- renameAndDefineVar "c"
        "x" <- renameAndDefineVar "x"
        shouldTranslateExprTo "a * x^2 + b * x + c"
          $  "addInt Shape Pos"
          ++ "  (addInt Shape Pos"
          ++ "    (mulInt Shape Pos a (powInt Shape Pos x (pure 2%Z)))"
          ++ "    (mulInt Shape Pos b x))"
          ++ "  c"

-- | Test group for translation of boolean expressions.
testConvertBool :: Spec
testConvertBool = context "boolean expressions" $ do
  it "translates 'True' correctly" $ shouldSucceed $ fromConverter $ do
    "True" `shouldTranslateExprTo` "True_ Shape Pos"

  it "translates 'False' correctly" $ shouldSucceed $ fromConverter $ do
    "False" `shouldTranslateExprTo` "False_ Shape Pos"

  it "translates conjunction correctly" $ shouldSucceed $ fromConverter $ do
    "x" <- renameAndDefineVar "x"
    "y" <- renameAndDefineVar "y"
    "x && y" `shouldTranslateExprTo` "andBool Shape Pos x y"

  it "translates disjunction correctly" $ shouldSucceed $ fromConverter $ do
    "x" <- renameAndDefineVar "x"
    "y" <- renameAndDefineVar "y"
    "x || y" `shouldTranslateExprTo` "orBool Shape Pos x y"

-- | Test group for translation of list expressions.
testConvertLists :: Spec
testConvertLists = context "list expressions" $ do
  it "translates empty list constructor correctly"
    $ shouldSucceed
    $ fromConverter
    $ shouldTranslateExprTo "[]" "Nil Shape Pos"

  it "translates non-empty list constructor correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "x"  <- renameAndDefineVar "x"
        "xs" <- renameAndDefineVar "xs"
        "x : xs" `shouldTranslateExprTo` "Cons Shape Pos x xs"

  it "translates list literal correctly" $ shouldSucceed $ fromConverter $ do
    "x1" <- renameAndDefineVar "x1"
    "x2" <- renameAndDefineVar "x2"
    "x3" <- renameAndDefineVar "x3"
    shouldTranslateExprTo "[x1, x2, x3]"
      $  "Cons Shape Pos x1 ("
      ++ "Cons Shape Pos x2 ("
      ++ "Cons Shape Pos x3 ("
      ++ "Nil Shape Pos)))"

-- | Test group for translation of tuple expressions.
testConvertTuples :: Spec
testConvertTuples = context "tuple expressions" $ do
  it "translates unit literals correctly" $ shouldSucceed $ fromConverter $ do
    "()" `shouldTranslateExprTo` "Tt Shape Pos"

  it "translates pair literals correctly" $ shouldSucceed $ fromConverter $ do
    "x" <- renameAndDefineVar "x"
    "y" <- renameAndDefineVar "y"
    "(x, y)" `shouldTranslateExprTo` "Pair_ Shape Pos x y"

  it "translates pair constructor correctly"
    $ shouldSucceed
    $ fromConverter
    $ do
        "x" <- renameAndDefineVar "x"
        "y" <- renameAndDefineVar "y"
        "(,) x y" `shouldTranslateExprTo` "Pair_ Shape Pos x y"
