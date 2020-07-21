-- | This module contains tests for "FreeC.IR.Similar".

module FreeC.IR.SimilarTests
  ( testSimilar
  )
where

import           Test.Hspec

import           FreeC.Test.Expectations
import           FreeC.Test.Parser

-- | Test group for 'FreeC.IR.Similar.similar' tests.
testSimilar :: Spec
testSimilar = describe "FreeC.IR.Similar" $ do
  testSimilarTypes
  testSimilarExprs
  testSimilarFuncDecls
  testSimilarTypeDecls

-- | Test group for 'FreeC.IR.Similar.Similar' instance of type schemes and
--   type expressions.
testSimilarTypes :: Spec
testSimilarTypes = context "types" $ do
  it "type constructors are similar to themselves" $ do
    foo <- expectParseTestType "Foo"
    foo `shouldBeSimilarTo` foo
  it "type constructors are not similar to other type constructors" $ do
    foo <- expectParseTestType "Foo"
    bar <- expectParseTestType "Bar"
    foo `shouldNotBeSimilarTo` bar
  it "type constructors are not similar to type variables" $ do
    foo <- expectParseTestType "Foo"
    a   <- expectParseTestType "a"
    foo `shouldNotBeSimilarTo` a

  it "free type variables are similar to themselves" $ do
    a <- expectParseTestType "a"
    a `shouldBeSimilarTo` a
  it "free type variables are not similar to other free type variables" $ do
    a <- expectParseTestType "a"
    b <- expectParseTestType "b"
    a `shouldNotBeSimilarTo` b

  it "bound type variables are similar to similarly bound type variables" $ do
    a <- expectParseTestTypeScheme "forall a. a"
    b <- expectParseTestTypeScheme "forall b. b"
    a `shouldBeSimilarTo` b
  it "bound type variables are not similar to unrelated bound type variables"
    $ do
        ab <- expectParseTestTypeScheme "forall a b. Foo a b"
        ba <- expectParseTestTypeScheme "forall b a. Foo a b"
        ab `shouldNotBeSimilarTo` ba
  it "bound type variables are not similar to right free type variables" $ do
    a  <- expectParseTestTypeScheme "forall a. a"
    a' <- expectParseTestTypeScheme "forall b. a"
    a `shouldNotBeSimilarTo` a'
  it "bound type variables are not similar to left free type variables" $ do
    a  <- expectParseTestTypeScheme "forall b. a"
    a' <- expectParseTestTypeScheme "forall a. a"
    a `shouldNotBeSimilarTo` a'

  it "type applications with similar children are similar" $ do
    fooA <- expectParseTestTypeScheme "forall a. Foo a"
    fooB <- expectParseTestTypeScheme "forall b. Foo b"
    fooA `shouldBeSimilarTo` fooB
  it "type applications with dissimilar left-hand sides are dissimilar" $ do
    fooA <- expectParseTestTypeScheme "forall a. Foo a"
    barB <- expectParseTestTypeScheme "forall b. Bar b"
    fooA `shouldNotBeSimilarTo` barB
  it "type applications with dissimilar right-hand sides are dissimilar" $ do
    fooA  <- expectParseTestTypeScheme "forall a b. Foo a"
    fooA' <- expectParseTestTypeScheme "forall b a. Foo a"
    fooA `shouldNotBeSimilarTo` fooA'

  it "function types with similar children are similar" $ do
    f <- expectParseTestTypeScheme "forall a b. a -> b"
    g <- expectParseTestTypeScheme "forall c d. c -> d"
    f `shouldBeSimilarTo` g
  it "function types with dissimilar right-hand sides are dissimilar" $ do
    f <- expectParseTestTypeScheme "forall a. a -> Foo"
    g <- expectParseTestTypeScheme "forall a. a -> Bar"
    f `shouldNotBeSimilarTo` g
  it "function types with dissimilar left-hand sides are dissimilar" $ do
    f <- expectParseTestTypeScheme "forall a. Foo -> a"
    g <- expectParseTestTypeScheme "forall a. Bar -> a"
    f `shouldNotBeSimilarTo` g

-- | Test group for 'FreeC.IR.Similar.Similar' instance of expressions.
testSimilarExprs :: Spec
testSimilarExprs = context "expressions" $ do
  it "constructors are similar to themselves" $ do
    foo <- expectParseTestExpr "Foo"
    foo `shouldBeSimilarTo` foo
  it "constructors are not similar to other constructors" $ do
    foo <- expectParseTestExpr "Foo"
    bar <- expectParseTestExpr "Bar"
    foo `shouldNotBeSimilarTo` bar
  it "constructors are not similar to variables" $ do
    foo <- expectParseTestExpr "Foo"
    a   <- expectParseTestExpr "a"
    foo `shouldNotBeSimilarTo` a

  it "integer literals are similar to themselves" $ do
    int <- expectParseTestExpr "42"
    int `shouldBeSimilarTo` int
  it "integer literals are not similar to other integer literals" $ do
    int1 <- expectParseTestExpr "42"
    int2 <- expectParseTestExpr "1337"
    int1 `shouldNotBeSimilarTo` int2

  it "error term 'undefined' is similar to itself" $ do
    e <- expectParseTestExpr "undefined"
    e `shouldBeSimilarTo` e
  it "error term 'error \"...\"' is similar to itself" $ do
    e <- expectParseTestExpr "error \"...\""
    e `shouldBeSimilarTo` e
  it "error term is not similar to error term with different message" $ do
    e1 <- expectParseTestExpr "error \"Hello\""
    e2 <- expectParseTestExpr "error \"World\""
    e1 `shouldNotBeSimilarTo` e2

  it "free variables are similar to themselves" $ do
    f <- expectParseTestExpr "f"
    f `shouldBeSimilarTo` f
  it "free variables are not similar to other free type variables" $ do
    f <- expectParseTestExpr "f"
    g <- expectParseTestExpr "g"
    f `shouldNotBeSimilarTo` g

  it "bound variables are similar to similarly bound variables" $ do
    e1 <- expectParseTestExpr "\\x -> x"
    e2 <- expectParseTestExpr "\\y -> y"
    e1 `shouldBeSimilarTo` e2
  it "bound variables are not similar to unrelated bound variables" $ do
    e1 <- expectParseTestExpr "\\x y -> x"
    e2 <- expectParseTestExpr "\\y x -> x"
    e1 `shouldNotBeSimilarTo` e2
  it "bound variables are not similar to right free bound variables" $ do
    e1 <- expectParseTestExpr "\\x -> x"
    e2 <- expectParseTestExpr "\\y -> x"
    e1 `shouldNotBeSimilarTo` e2
  it "bound variables are not similar to left free bound variables" $ do
    e1 <- expectParseTestExpr "\\y -> x"
    e2 <- expectParseTestExpr "\\x -> x"
    e1 `shouldNotBeSimilarTo` e2

  it "expressions with dissimilar type annotation are not similar" $ do
    e1 <- expectParseTestExpr "x :: Foo"
    e2 <- expectParseTestExpr "x :: Bar"
    e1 `shouldNotBeSimilarTo` e2
  it "expressions with and without type annotation are not similar" $ do
    e1 <- expectParseTestExpr "x :: a"
    e2 <- expectParseTestExpr "x"
    e1 `shouldNotBeSimilarTo` e2

  it "lambda abstractions with different arity are not similar" $ do
    e1 <- expectParseTestExpr "\\x y -> x"
    e2 <- expectParseTestExpr "\\x -> x"
    e1 `shouldNotBeSimilarTo` e2
  it "lambda abstractions with dissimilar argument annotations are not similar"
    $ do
        e1 <- expectParseTestExpr "\\(x :: Foo) -> x"
        e2 <- expectParseTestExpr "\\(x :: Bar) -> x"
        e1 `shouldNotBeSimilarTo` e2
  it "lambda abstractions with and without argument annotations are not similar"
    $ do
        e1 <- expectParseTestExpr "\\(x :: Foo) -> x"
        e2 <- expectParseTestExpr "\\x -> x"
        e1 `shouldNotBeSimilarTo` e2

  it "applications with similar children are similar" $ do
    fooX <- expectParseTestExpr "\\x -> Foo x"
    fooY <- expectParseTestExpr "\\y -> Foo y"
    fooX `shouldBeSimilarTo` fooY
  it "applications with dissimilar left-hand sides are dissimilar" $ do
    fooX <- expectParseTestExpr "\\x -> Foo x"
    barY <- expectParseTestExpr "\\y -> Bar y"
    fooX `shouldNotBeSimilarTo` barY
  it "applications with dissimilar right-hand sides are dissimilar" $ do
    fooX  <- expectParseTestExpr "\\x y -> Foo x"
    fooX' <- expectParseTestExpr "\\y a -> Foo a"
    fooX `shouldNotBeSimilarTo` fooX'

  it "visible applications of dissimilar types are not similar" $ do
    fa <- expectParseTestExpr "f @a"
    fb <- expectParseTestExpr "f @b"
    fa `shouldNotBeSimilarTo` fb

  it "if expressions with similar children are similar" $ do
    e1 <- expectParseTestExpr "\\x y z -> if x then y else z"
    e2 <- expectParseTestExpr "\\c t f -> if c then t else f"
    e1 `shouldBeSimilarTo` e2
  it "if expressions with dissimilar conditions are not similar" $ do
    e1 <- expectParseTestExpr "\\y z -> if True then y else z"
    e2 <- expectParseTestExpr "\\t f -> if False then t else f"
    e1 `shouldNotBeSimilarTo` e2
  it "if expressions with dissimilar then branches are not similar" $ do
    e1 <- expectParseTestExpr "\\x z -> if x then Foo else z"
    e2 <- expectParseTestExpr "\\c f -> if c then Bar else f"
    e1 `shouldNotBeSimilarTo` e2
  it "if expressions with dissimilar else branches are not similar" $ do
    e1 <- expectParseTestExpr "\\x y -> if x then y else Foo"
    e2 <- expectParseTestExpr "\\c t -> if c then t else Bar"
    e1 `shouldNotBeSimilarTo` e2

  it "case expressions with similar children are similar" $ do
    e1 <- expectParseTestExpr "\\xs -> case xs of { ([]) -> 0; (:) x xs' -> x }"
    e2 <- expectParseTestExpr "\\ys -> case ys of { ([]) -> 0; (:) y ys' -> y }"
    e1 `shouldBeSimilarTo` e2
  it "case expressions with dissimilar scrutinees are not similar" $ do
    e1 <- expectParseTestExpr "case xs of { ([]) -> 0; (:) x xs' -> x }"
    e2 <- expectParseTestExpr "case ys of { ([]) -> 0; (:) y ys' -> y }"
    e1 `shouldNotBeSimilarTo` e2
  it "case expressions with unordered alternatives are not similar" $ do
    e1 <- expectParseTestExpr "\\xs -> case xs of { (:) x xs' -> x; ([]) -> 0 }"
    e2 <- expectParseTestExpr "\\ys -> case ys of { ([]) -> 0; (:) y ys' -> y }"
    e1 `shouldNotBeSimilarTo` e2
  it "case expressions with dissimilar alternatives are not similar" $ do
    e1 <- expectParseTestExpr "\\xs -> case xs of { ([]) -> 0; (:) x xs' -> x }"
    e2 <- expectParseTestExpr "\\ys -> case ys of { ([]) -> 1; (:) y ys' -> y }"
    e1 `shouldNotBeSimilarTo` e2
  it "case expressions with different number of alternatives are not similar"
    $ do
        e1 <- expectParseTestExpr "case xy of { (,) x y -> x }"
        e2 <- expectParseTestExpr "case xy of {  }"
        e1 `shouldNotBeSimilarTo` e2
  it "alternatives with different constructor patterns are not similar" $ do
    e1 <- expectParseTestExpr "\\xs -> case xs of { ([]) -> 0; (:) x xs' -> x }"
    e2 <- expectParseTestExpr "\\ys -> case ys of { Nil -> 0; Cons y ys' -> y }"
    e1 `shouldNotBeSimilarTo` e2
  it "alternatives with dissimilar variable type annotations are not similar"
    $ do
        e1 <- expectParseTestExpr "case xy of { (,) (x :: Foo) y -> x }"
        e2 <- expectParseTestExpr "case xy of { (,) (x :: Bar) y -> x }"
        e1 `shouldNotBeSimilarTo` e2
  it "alternatives with different number of variable patterns are not similar"
    $ do
        e1 <- expectParseTestExpr "case xy of { (,) (x :: Foo) y -> x }"
        e2 <- expectParseTestExpr "case xy of { (,) (x :: Bar) y -> x }"
        e1 `shouldNotBeSimilarTo` e2

-- | Test group for 'FreeC.IR.Similar.Similar' instance of function
--   declarations.
testSimilarFuncDecls :: Spec
testSimilarFuncDecls = context "function declarations" $ do
  it "nullary functions are similar" $ do
    f1 <- expectParseTestFuncDecl "f = ()"
    f2 <- expectParseTestFuncDecl "f = ()"
    f1 `shouldBeSimilarTo` f2
  it "functions with different names are not similar" $ do
    f <- expectParseTestFuncDecl "f = ()"
    g <- expectParseTestFuncDecl "g = ()"
    f `shouldNotBeSimilarTo` g
  it "functions with similar right-hand side are similar" $ do
    fx <- expectParseTestFuncDecl "f x = x"
    fy <- expectParseTestFuncDecl "f y = y"
    fx `shouldBeSimilarTo` fy
  it "functions with dissimilar right-hand side are not similar" $ do
    fx <- expectParseTestFuncDecl "f x y = x"
    fy <- expectParseTestFuncDecl "f y x = x"
    fx `shouldNotBeSimilarTo` fy
  it "functions with dissimilar argument type annotations are not similar" $ do
    fx <- expectParseTestFuncDecl "f (x :: Foo) = x"
    fy <- expectParseTestFuncDecl "f (y :: Bar) = y"
    fx `shouldNotBeSimilarTo` fy
  it "functions with and without argument type annotations are not similar" $ do
    fx <- expectParseTestFuncDecl "f (x :: Foo) = x"
    fy <- expectParseTestFuncDecl "f y = y"
    fx `shouldNotBeSimilarTo` fy
  it "functions with strict and non-strict arguments are not similar" $ do
    fx <- expectParseTestFuncDecl "f !x = x"
    fy <- expectParseTestFuncDecl "f y = y"
    fx `shouldNotBeSimilarTo` fy
  it "functions with and without return type annotations are not similar" $ do
    fx <- expectParseTestFuncDecl "f x :: Foo = x"
    fy <- expectParseTestFuncDecl "f y = y"
    fx `shouldNotBeSimilarTo` fy
  it "functions with different arities are not similar" $ do
    fxz <- expectParseTestFuncDecl "f x z = x"
    fy  <- expectParseTestFuncDecl "f y = y"
    fxz `shouldNotBeSimilarTo` fy
  it "type arguments bind type variables in argument type annotations" $ do
    fab <- expectParseTestFuncDecl "f @a (x :: a) = x"
    fb  <- expectParseTestFuncDecl "f @b (x :: b) = x"
    fab `shouldBeSimilarTo` fb
  it "type arguments bind type variables in return type annotations" $ do
    fa <- expectParseTestFuncDecl "f @a :: a = undefined"
    fb <- expectParseTestFuncDecl "f @b :: b = undefined"
    fa `shouldBeSimilarTo` fb
  it "type arguments bind type variables in on right-hand side" $ do
    fa <- expectParseTestFuncDecl "f @a = undefined @a"
    fb <- expectParseTestFuncDecl "f @b = undefined @b"
    fa `shouldBeSimilarTo` fb
  it "functions with different type arities are not similar" $ do
    fa <- expectParseTestFuncDecl "f @a @b = undefined"
    fb <- expectParseTestFuncDecl "f @a = undefined"
    fa `shouldNotBeSimilarTo` fb

-- | Test group for 'FreeC.IR.Similar.Similar' instance of type-level
--   declarations.
testSimilarTypeDecls :: Spec
testSimilarTypeDecls = do
  context "type synonym declarations" $ do
    it "nullary type synonyms are similar" $ do
      foo1 <- expectParseTestTypeDecl "type Foo = ()"
      foo2 <- expectParseTestTypeDecl "type Foo = ()"
      foo1 `shouldBeSimilarTo` foo2
    it "type synonyms with different names are not similar" $ do
      foo <- expectParseTestTypeDecl "type Foo = ()"
      bar <- expectParseTestTypeDecl "type Bar = ()"
      foo `shouldNotBeSimilarTo` bar
    it "type synonyms with similar right-hand side are similar" $ do
      foo1 <- expectParseTestTypeDecl "type Foo a = Bar a"
      foo2 <- expectParseTestTypeDecl "type Foo b = Bar b"
      foo1 `shouldBeSimilarTo` foo2
    it "type synonyms with dissimilar right-hand side are not similar" $ do
      foo1 <- expectParseTestTypeDecl "type Foo a b = Bar a"
      foo2 <- expectParseTestTypeDecl "type Foo b a = Bar a"
      foo1 `shouldNotBeSimilarTo` foo2
    it "type synonyms with different number of type arguments are not similar"
      $ do
          foo1 <- expectParseTestTypeDecl "type Foo a = Bar a"
          foo2 <- expectParseTestTypeDecl "type Foo a b = Bar a"
          foo1 `shouldNotBeSimilarTo` foo2
  context "data type declarations" $ do
    it "nullary data types are similar to themselves" $ do
      foo <- expectParseTestTypeDecl "data Foo"
      foo `shouldBeSimilarTo` foo
    it "data types with different names are not similar" $ do
      foo <- expectParseTestTypeDecl "data Foo"
      bar <- expectParseTestTypeDecl "data Bar"
      foo `shouldNotBeSimilarTo` bar
    it "data types with similar constructors are similar" $ do
      foo1 <- expectParseTestTypeDecl "data Foo a = Bar a"
      foo2 <- expectParseTestTypeDecl "data Foo b = Bar b"
      foo1 `shouldBeSimilarTo` foo2
    it "data types with dissimilar constructors are not similar" $ do
      foo1 <- expectParseTestTypeDecl "data Foo a b = Bar a"
      foo2 <- expectParseTestTypeDecl "data Foo b a = Bar a"
      foo1 `shouldNotBeSimilarTo` foo2
    it "data types with different number of type arguments are not similar" $ do
      foo1 <- expectParseTestTypeDecl "data Foo a"
      foo2 <- expectParseTestTypeDecl "data Foo a b"
      foo1 `shouldNotBeSimilarTo` foo2
    it "data types with unordered constructors are not similar" $ do
      foo1 <- expectParseTestTypeDecl "data Foo = Foo | Bar"
      foo2 <- expectParseTestTypeDecl "data Foo = Bar | Foo"
      foo1 `shouldNotBeSimilarTo` foo2
    it "constructors with different names are not similar" $ do
      fooFoo <- expectParseTestTypeDecl "data Foo = Foo"
      fooBar <- expectParseTestTypeDecl "data Foo = Bar"
      fooFoo `shouldNotBeSimilarTo` fooBar
    it "constructors with different number of fields are not similar" $ do
      foo1 <- expectParseTestTypeDecl "data Foo a = Foo a"
      foo2 <- expectParseTestTypeDecl "data Foo a = Foo a a"
      foo1 `shouldNotBeSimilarTo` foo2
