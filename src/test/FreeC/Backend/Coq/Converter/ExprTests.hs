-- | This module contains tests for "FreeC.Backend.Coq.Converter.Expr".
module FreeC.Backend.Coq.Converter.ExprTests ( testConvertExpr ) where

import           Test.Hspec

import           FreeC.Backend.Coq.Converter.Expr
import           FreeC.Backend.Coq.Pretty         ()
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Test.Environment
import           FreeC.Test.Expectations
import           FreeC.Test.Parser

-------------------------------------------------------------------------------
-- Expectation Setters                                                       --
-------------------------------------------------------------------------------
-- | Parses the given IR expression, converts it to Coq using 'convertExpr'
--   and sets the expectation that the resulting AST is equal to the given
--   output when pretty printed modulo whitespace.
shouldConvertExprTo :: String -> String -> Converter Expectation
shouldConvertExprTo inputStr expectedOutputStr = do
  input <- parseTestExpr inputStr
  output <- convertExpr input
  return (output `prettyShouldBe` expectedOutputStr)

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------
-- | Test group for 'convertExpr' tests.
testConvertExpr :: Spec
testConvertExpr = describe "FreeC.Backend.Coq.Converter.Expr.convertExpr" $ do
  testConvertConApp
  testConvertFuncApp
  testConvertIf
  testConvertCase
  testConvertLet
  testConvertLambda
  testConvertExprTypeAnnotations
  testConvertTypeAppExprs
  testConvertInteger
  testConvertUndefined
  testConvertError

-------------------------------------------------------------------------------
-- Constructor Applications                                                  --
-------------------------------------------------------------------------------
-- | Test group for translation of constructor application expressions.
testConvertConApp :: Spec
testConvertConApp = context "constructor applications" $ do
  it "converts nullary constructor applications correctly"
    $ shouldSucceedWith
    $ do
      "D" <- defineTestTypeCon "D" 0 ["C"]
      ("c", "C") <- defineTestCon "C" 0 "D"
      "C" `shouldConvertExprTo` "C Shape Pos"
  it "converts polymorphic nullary constructor applications correctly"
    $ shouldSucceedWith
    $ do
      "D" <- defineTestTypeCon "D" 1 ["C"]
      ("c", "C") <- defineTestCon "C" 0 "forall a. D a"
      "a" <- defineTestTypeVar "a"
      "C @a" `shouldConvertExprTo` "@C Shape Pos a"
  it "converts constructor applications correctly" $ shouldSucceedWith $ do
    "D" <- defineTestTypeCon "D" 0 ["C"]
    (_, "C") <- defineTestCon "C" 3 "forall a b. a -> b -> D"
    "a" <- defineTestTypeVar "a"
    "b" <- defineTestTypeVar "b"
    "x" <- defineTestVar "x"
    "y" <- defineTestVar "y"
    "C @a @b x y" `shouldConvertExprTo` "@C Shape Pos a b x y"
  it "converts partial constructor applications correctly"
    $ shouldSucceedWith
    $ do
      "D" <- defineTestTypeCon "D" 0 ["C"]
      (_, "C") <- defineTestCon "C" 3 "forall a b. a -> b -> D"
      "a" <- defineTestTypeVar "a"
      "b" <- defineTestTypeVar "b"
      "x" <- defineTestVar "x"
      "C @a @b x" `shouldConvertExprTo` "@C Shape Pos a b x"
  it "converts unapplied constructors correctly" $ shouldSucceedWith $ do
    "D" <- defineTestTypeCon "D" 0 ["C"]
    (_, "C") <- defineTestCon "C" 3 "forall a b. a -> b -> D"
    "a" <- defineTestTypeVar "a"
    "b" <- defineTestTypeVar "b"
    "C @a @b" `shouldConvertExprTo` "@C Shape Pos a b"
  it "requires visible type applications of constructors" $ do
    input <- expectParseTestExpr "C"
    shouldFail $ do
      "D" <- defineTestTypeCon "D" 0 ["C"]
      (_, "C") <- defineTestCon "C" 3 "forall a. a -> D"
      convertExpr input

-------------------------------------------------------------------------------
-- Function Applications                                                     --
-------------------------------------------------------------------------------
-- | Test group for translation of function application expressions.
testConvertFuncApp :: Spec
testConvertFuncApp = context "function applications" $ do
  it "converts nullary function (pattern-binding) applications correctly"
    $ shouldSucceedWith
    $ do
      "f" <- defineTestFunc "f" 0 "forall a. a"
      "a" <- defineTestTypeVar "a"
      "f @a" `shouldConvertExprTo` "@f Shape Pos a"
  it "converts complete function applications correctly" $ shouldSucceedWith $ do
    "f" <- defineTestFunc "f" 3 "forall a. a -> a -> a"
    "a" <- defineTestTypeVar "a"
    "x" <- defineTestVar "x"
    "y" <- defineTestVar "y"
    "f @a x y" `shouldConvertExprTo` "@f Shape Pos a x y"
  it "converts partial function applications correctly" $ shouldSucceedWith $ do
    "f" <- defineTestFunc "f" 3 "forall a. a -> a -> a"
    "a" <- defineTestTypeVar "a"
    "x" <- defineTestVar "x"
    "f @a x" `shouldConvertExprTo` "@f Shape Pos a x"
  it "converts unapplied functions correctly" $ shouldSucceedWith $ do
    "f" <- defineTestFunc "f" 3 "forall a. a -> a -> a"
    "a" <- defineTestTypeVar "a"
    "f @a" `shouldConvertExprTo` "@f Shape Pos a"
  it "converts applications of partial functions correctly"
    $ shouldSucceedWith
    $ do
      "f" <- definePartialTestFunc "f" 1 "forall a b. a -> b"
      "a" <- defineTestTypeVar "a"
      "b" <- defineTestTypeVar "b"
      "x" <- defineTestVar "x"
      "f @a @b x" `shouldConvertExprTo` "@f Shape Pos P a b x"
  it "converts applications of function expressions correctly"
    $ shouldSucceedWith
    $ do
      "e1" <- defineTestVar "e1"
      "e2" <- defineTestVar "e2"
      "e1 e2" `shouldConvertExprTo` "e1 >>= (fun e3 => e3 e2)"
  it "converts applications of functions that return functions correctly"
    $ shouldSucceedWith
    $ do
      "f" <- defineTestFunc "f" 1 "forall a. a -> a -> a"
      "a" <- defineTestTypeVar "a"
      "x" <- defineTestVar "x"
      "y" <- defineTestVar "y"
      shouldConvertExprTo "f @a x y" "@f Shape Pos a x >>= (fun f0 => f0 y)"
  it "requires visible type applications of functions" $ do
    input <- expectParseTestExpr "f"
    shouldFail $ do
      "f" <- defineTestFunc "f" 0 "forall a. a"
      convertExpr input
  it "converts function applications with one strict argument correctly"
    $ shouldSucceedWith
    $ do
      "f" <- defineStrictTestFunc "f" [True] "forall a. a -> a"
      "a" <- defineTestTypeVar "a"
      "x" <- defineTestVar "x"
      "f @a x"
        `shouldConvertExprTo` "x >>= (fun (x0 : a) => @f Shape Pos a x0)"
  it "converts function applications with two strict arguments correctly"
    $ shouldSucceedWith
    $ do
      "f" <- defineStrictTestFunc "f" [True, True] "forall a. a -> a -> a"
      "a" <- defineTestTypeVar "a"
      "x" <- defineTestVar "x"
      "y" <- defineTestVar "y"
      shouldConvertExprTo "f @a x y"
        $ "x >>= (fun (x0 : a) =>"
        ++ "  y >>= (fun (y0 : a) => @f Shape Pos a x0 y0))"
  it ("converts function applications with one non-strict and one"
      ++ "strict argument correctly")
    $ shouldSucceedWith
    $ do
      "f" <- defineStrictTestFunc "f" [False, True] "forall a. a -> a -> a"
      "a" <- defineTestTypeVar "a"
      "x" <- defineTestVar "x"
      "y" <- defineTestVar "y"
      "f @a x y"
        `shouldConvertExprTo` "y >>= (fun (y0 : a) => @f Shape Pos a x y0)"

-------------------------------------------------------------------------------
-- @if@-Expressions                                                          --
-------------------------------------------------------------------------------
-- | Test group for translation of @if@-expressions.
testConvertIf :: Spec
testConvertIf = context "if expressions" $ do
  it "converts if expressions correctly" $ shouldSucceedWith $ do
    "Bool" <- defineTestTypeCon "Prelude.Bool" 0 []
    "e1" <- defineTestVar "e1"
    "e2" <- defineTestVar "e2"
    "e3" <- defineTestVar "e3"
    shouldConvertExprTo "if e1 then e2 else e3"
      $ "e1 >>= (fun (e4 : Bool Shape Pos) => if e4 then e2 else e3)"
  it "there is no name conflict with custom `Bool`" $ shouldSucceedWith $ do
    "Bool" <- defineTestTypeCon "M1.Bool" 0 []
    "Bool0" <- defineTestTypeCon "Prelude.Bool" 0 []
    "Bool1" <- defineTestTypeCon "M2.Bool" 0 []
    "e1" <- defineTestVar "e1"
    "e2" <- defineTestVar "e2"
    "e3" <- defineTestVar "e3"
    shouldConvertExprTo "if e1 then e2 else e3"
      $ "e1 >>= (fun (e4 : Bool0 Shape Pos) => if e4 then e2 else e3)"

-------------------------------------------------------------------------------
-- @case@-Expressions                                                        --
-------------------------------------------------------------------------------
-- | Test group for translation of @case@-expressions.
testConvertCase :: Spec
testConvertCase = context "case expressions" $ do
  it "simplifies matches with only one alternative (during pretty printing)"
    $ shouldSucceedWith
    $ do
      "e" <- defineTestVar "e"
      "e'" <- defineTestVar "e'"
      "D" <- defineTestTypeCon "D" 0 ["C"]
      ("c", _) <- defineTestCon "C" 0 "D"
      "case e of { C -> e' }" `shouldConvertExprTo` "e >>= (fun '(c) => e')"
  it "uses data (not smart) constructors" $ shouldSucceedWith $ do
    "e" <- defineTestVar "e"
    "e1" <- defineTestVar "e1"
    "e2" <- defineTestVar "e2"
    "D" <- defineTestTypeCon "D" 0 ["C1", "C2"]
    ("c1", _) <- defineTestCon "C1" 0 "D"
    ("c2", _) <- defineTestCon "C2" 0 "D"
    shouldConvertExprTo "case e of { C1 -> e1;  C2 -> e2 }"
      $ "e >>= (fun e0 =>"
      ++ "  match e0 with"
      ++ "  | c1 => e1"
      ++ "  | c2 => e2"
      ++ "  end)"
  it "allows case expressions to shadow local variables" $ shouldSucceedWith $ do
    "List" <- defineTestTypeCon "List" 1 ["Nil", "Cons"]
    ("nil", _) <- defineTestCon "Nil" 0 "forall a. List a"
    ("cons", _) <- defineTestCon "Cons" 2 "forall a. a -> List a -> List a"
    "e" <- defineTestVar "e"
    "x" <- defineTestVar "x"
    shouldConvertExprTo "case e of { Nil -> x; Cons x xs -> x }"
      $ "e >>= (fun e0 =>"
      ++ "  match e0 with"
      ++ "  | nil => x"
      ++ "  | cons x0 xs => x0"
      ++ "  end)"
  it "allows case expressions to shadow local variables" $ shouldSucceedWith $ do
    "AB" <- defineTestTypeCon "AB" 0 ["A", "B"]
    ("a", _) <- defineTestCon "A" 0 "Unit"
    ("b", _) <- defineTestCon "B" 0 "Unit"
    "x" <- defineTestVar "x"
    "x0" <- defineTestVar "x0"
    shouldConvertExprTo
      "case x of { A -> case x of { A -> x; B -> x }; B -> x }"
      $ "x >>= (fun x1 =>"
      ++ "  match x1 with"
      ++ "  | a => x >>= (fun x2 =>"
      ++ "    match x2 with"
      ++ "    | a => x"
      ++ "    | b => x"
      ++ "    end)"
      ++ "  | b => x"
      ++ "  end)"

-------------------------------------------------------------------------------
-- Let Expressions                                                           --
-------------------------------------------------------------------------------
-- | Test group for translation of Let expressions.
testConvertLet :: Spec
testConvertLet = context "let expressions" $ do
  it "translates a let expression with a single bind correctly"
    $ shouldSucceedWith
    $ do
      "add" <- defineTestFunc "add" 2 "Integer -> Integer -> Integer"
      "Integer" <- defineTestTypeCon "Integer" 0 []
      "x" <- defineTestVar "x"
      shouldConvertExprTo "let {(x' :: Integer) = x} in (add x' x')"
        $ "@share Shape Pos (S Shape Pos _) (Integer Shape Pos) _"
        ++ "  x >>= (fun (x' : Free Shape Pos (Integer Shape Pos)) =>"
        ++ "    add Shape Pos x' x')"
  it "translates a let expression with two binds correctly"
    $ shouldSucceedWith
    $ do
      "add" <- defineTestFunc "add" 2 "Integer -> Integer -> Integer"
      "Integer" <- defineTestTypeCon "Integer" 0 []
      "x" <- defineTestVar "x"
      "y" <- defineTestVar "y"
      shouldConvertExprTo
        "let {(x' :: Integer) = x; (y' :: Integer) = y} in (add x' y')"
        $ "@share Shape Pos (S Shape Pos _) (Integer Shape Pos) _ x"
        ++ "  >>= (fun (x' : Free Shape Pos (Integer Shape Pos)) =>"
        ++ "    @share Shape Pos (S Shape Pos _) (Integer Shape Pos) _ y"
        ++ "      >>= (fun (y' : Free Shape Pos (Integer Shape Pos)) =>"
        ++ "        add Shape Pos x' y'))"

-------------------------------------------------------------------------------
-- Lambda Abstractions                                                       --
-------------------------------------------------------------------------------
-- | Test group for translation of lambda abstractions.
testConvertLambda :: Spec
testConvertLambda = context "lambda abstractions" $ do
  it "translates single argument lambda abstractions correctly"
    $ shouldSucceedWith
    $ do
      "e" <- defineTestVar "e"
      "\\x -> e" `shouldConvertExprTo` "pure (fun x => e)"
  it "translates lambda abstractions with type annotated arguments correctly"
    $ shouldSucceedWith
    $ do
      "t" <- defineTestTypeVar "t"
      "e" <- defineTestVar "e"
      shouldConvertExprTo "\\(x :: t) -> e"
        "pure (fun (x : Free Shape Pos t) => e)"
  it "translates multi argument lambda abstractions correctly"
    $ shouldSucceedWith
    $ do
      "e" <- defineTestVar "e"
      "\\x y -> e" `shouldConvertExprTo` "pure (fun x => pure (fun y => e))"
  it "allows lambda abstractions to shadow local variables"
    $ shouldSucceedWith
    $ do
      "x" <- defineTestVar "x"
      "\\x -> x" `shouldConvertExprTo` "pure (fun x0 => x0)"

-------------------------------------------------------------------------------
-- Type Signatures                                                           --
-------------------------------------------------------------------------------
-- | Test group for translation of expressions with type annotations.
testConvertExprTypeAnnotations :: Spec
testConvertExprTypeAnnotations = context "type annotations" $ do
  it "ignores expression type annotations" $ shouldSucceedWith $ do
    "42 :: Integer" `shouldConvertExprTo` "pure 42%Z"

-- | Test group for translation of visibly applied expressions.
testConvertTypeAppExprs :: Spec
testConvertTypeAppExprs = context "visible type applications" $ do
  it "translates visible type applications to explicit applications in Coq"
    $ shouldSucceedWith
    $ do
      "Bool" <- defineTestTypeCon "Bool" 0 []
      "List" <- defineTestTypeCon "List" 1 ["Nil"]
      (_, "Nil") <- defineTestCon "Nil" 0 "forall a. List a"
      "Nil @Bool" `shouldConvertExprTo` "@Nil Shape Pos (Bool Shape Pos)"

-------------------------------------------------------------------------------
-- Integer Expressions                                                       --
-------------------------------------------------------------------------------
-- | Test group for translation of integer expressions.
testConvertInteger :: Spec
testConvertInteger = context "integer expressions" $ do
  it "translates zero correctly"
    $ shouldSucceedWith
    $ shouldConvertExprTo "0" "pure 0%Z"
  it "translates positive decimal integer literals correctly"
    $ shouldSucceedWith
    $ shouldConvertExprTo "42" "pure 42%Z"
  it "translates hexadecimal integer literals correctly"
    $ shouldSucceedWith
    $ shouldConvertExprTo "0xA2" "pure 162%Z"
  it "translates octal integer literals correctly"
    $ shouldSucceedWith
    $ shouldConvertExprTo "0o755" "pure 493%Z"
  it "translates negative decimal integer literals correctly"
    $ shouldSucceedWith
    $ shouldConvertExprTo "-42" "pure (- 42)%Z"

-- | Test group for translation of undefined expressions.
testConvertUndefined :: Spec
testConvertUndefined = context "undefined expressions" $ do
  it "translates undefined expressions correctly" $ shouldSucceedWith $ do
    "a" <- defineTestTypeVar "a"
    shouldConvertExprTo "undefined @a" "@undefined Shape Pos P a"
  it "translates undefined expressions applied to arguments correctly"
    $ shouldSucceedWith
    $ do
      "a" <- defineTestTypeVar "a"
      "b" <- defineTestTypeVar "b"
      "c" <- defineTestTypeVar "c"
      "x" <- defineTestVar "x"
      "y" <- defineTestVar "y"
      shouldConvertExprTo "undefined @(a->b->c) x y"
        $ "(@undefined Shape Pos P (Free Shape Pos a ->"
        ++ " Free Shape Pos (Free Shape Pos b -> Free Shape Pos c))"
        ++ " >>= (fun f => f x))"
        ++ " >>= (fun f => f y)"

-- | Test group for translation of undefined expressions.
testConvertError :: Spec
testConvertError = context "error expressions" $ do
  it "translates error expressions correctly" $ shouldSucceedWith $ do
    "a" <- defineTestTypeVar "a"
    shouldConvertExprTo "error @a \"message\""
      "@error Shape Pos P a \"message\"%string"
  it "translates error expressions applied to arguments correctly"
    $ shouldSucceedWith
    $ do
      "a" <- defineTestTypeVar "a"
      "b" <- defineTestTypeVar "b"
      "c" <- defineTestTypeVar "c"
      "x" <- defineTestVar "x"
      "y" <- defineTestVar "y"
      shouldConvertExprTo "error @(a->b->c) \"message\" x y"
        $ "(@error Shape Pos P (Free Shape Pos a ->"
        ++ " Free Shape Pos (Free Shape Pos b -> Free Shape Pos c))"
        ++ " \"message\"%string"
        ++ " >>= (fun f => f x))"
        ++ " >>= (fun f => f y)"
