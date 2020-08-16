-- | This module contains tests for "FreeC.Pass.EtaConversionPass".

module FreeC.Pass.EtaConversionPassTests where

import           Test.Hspec

import           FreeC.Environment
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Pass.EtaConversionPass
import           FreeC.Test.Parser
import           FreeC.Test.Environment
import           FreeC.Test.Expectations

-------------------------------------------------------------------------------
-- Expectation setters                                                       --
-------------------------------------------------------------------------------

-- | Parses the given function declaration, applies the eta conversion
--   pass and sets the expectation that the resulting function declaration
--   is 'FreeC.IR.Similar.similar' to the expected output.
shouldEtaConvertTopLevel :: String -> String -> Converter Expectation
shouldEtaConvertTopLevel inputStr expectedOutputStr = do
  input          <- parseTestFuncDecl inputStr
  expectedOutput <- parseTestFuncDecl expectedOutputStr
  output         <- etaConvertFuncDecl input
  return (output `shouldBeSimilarTo` expectedOutput)

-- | Parses the given expressions, applies the eta conversion
--   pass and sets the expectation that the resulting expression
--   is 'FreeC.IR.Similar.similar' to the expected output.
shouldEtaConvert :: String -> String -> Converter Expectation
shouldEtaConvert inputStr expectedOutputStr = do
  input          <- parseTestExpr inputStr
  expectedOutput <- parseTestExpr expectedOutputStr
  output         <- etaConvertExpr input
  return (output `shouldBeSimilarTo` expectedOutput)

-------------------------------------------------------------------------------
-- Tests                                                                     --
-------------------------------------------------------------------------------

-- | Test group for 'etaConversionPass' tests.
testEtaConversionPass :: Spec
testEtaConversionPass = describe "FreeC.Pass.EtaConversionPass" $ do
  testEtaConvertFuncDecl
  testEtaConvertExpr

-- | Test group for 'etaConvertFuncDecl' tests.
testEtaConvertFuncDecl :: Spec
testEtaConvertFuncDecl = context "etaConvertFuncDecl" $ do
  it
      (  "applies functions under-applied on the top-level"
      ++ "to one missing argument"
      )
    $ shouldSucceedWith
    $ do
        _ <- defineTestTypeCon "Foo" 0 []
        _ <- defineTestFunc "f" 0 "Foo -> Foo"
        _ <- defineTestFunc "g" 2 "Foo -> Foo -> Foo"
        shouldEtaConvertTopLevel "f :: Foo -> Foo = g Foo"
                                 "f (y :: Foo) :: Foo = g Foo y"
  it
      (  "applies functions under-applied on the top-level"
      ++ "to multiple missing arguments"
      )
    $ shouldSucceedWith
    $ do
        _ <- defineTestTypeCon "Foo" 0 []
        _ <- defineTestFunc "f" 0 "Foo -> Foo -> Foo"
        _ <- defineTestFunc "g" 3 "Foo -> Foo -> Foo -> Foo"
        shouldEtaConvertTopLevel "f :: Foo -> Foo -> Foo = g Foo"
                                 "f (x :: Foo) (y :: Foo) :: Foo = g Foo x y"
  it "updates function arity in environment" $ shouldSucceedWith $ do
    _     <- defineTestTypeCon "Foo" 0 []
    _     <- defineTestFunc "f" 0 "Foo -> Foo"
    _     <- defineTestFunc "g" 2 "Foo -> Foo -> Foo"
    input <- parseTestFuncDecl "f :: Foo -> Foo = g Foo"
    _     <- etaConvertFuncDecl input
    arity <- inEnv $ lookupArity IR.ValueScope (IR.UnQual (IR.Ident "f"))
    return (arity `shouldBe` Just 1)
  it "updates function return type in environment" $ shouldSucceedWith $ do
    _            <- defineTestTypeCon "Foo" 0 []
    _            <- defineTestFunc "f" 0 "Foo -> Foo"
    _            <- defineTestFunc "g" 2 "Foo -> Foo -> Foo"
    input        <- parseTestFuncDecl "f :: Foo -> Foo = g Foo"
    _            <- etaConvertFuncDecl input
    expectedType <- parseTestType "Foo"
    returnType   <- inEnv
      $ lookupReturnType IR.ValueScope (IR.UnQual (IR.Ident "f"))
    return (returnType `shouldBeSimilarTo` Just expectedType)
  it "updates function argument type in environment" $ shouldSucceedWith $ do
    _            <- defineTestTypeCon "Foo" 0 []
    _            <- defineTestFunc "f" 0 "Foo -> Foo"
    _            <- defineTestFunc "g" 2 "Foo -> Foo -> Foo"
    input        <- parseTestFuncDecl "f :: Foo -> Foo = g Foo"
    _            <- etaConvertFuncDecl input
    expectedType <- parseTestType "Foo"
    argTypes <- inEnv $ lookupArgTypes IR.ValueScope (IR.UnQual (IR.Ident "f"))
    return (argTypes `shouldBeSimilarTo` Just [expectedType])
  it "applies under-applied function that is if-expression to missing argument"
    $ shouldSucceedWith
    $ do
        _ <- defineTestTypeCon "Foo" 0 []
        _ <- defineTestFunc "f" 1 "Bool -> Foo -> Foo"
        _ <- defineTestFunc "g" 2 "Foo -> Foo -> Foo"
        shouldEtaConvertTopLevel
          "f (b :: Bool) :: Foo -> Foo = if b then g Foo else g Foo"
          "f (b :: Bool) (y :: Foo) :: Foo = if b then g Foo y else g Foo y"
  it
      (  "applies under-applied function that is if-expression"
      ++ "to minimal number of missing argument in both branches"
      )
    $ shouldSucceedWith
    $ do
        _ <- defineTestTypeCon "Foo" 0 []
        _ <- defineTestFunc "f" 1 "Bool -> Foo -> Foo"
        _ <- defineTestFunc "g" 2 "Foo -> Foo -> Foo"
        _ <- defineTestFunc "h" 1 "Foo -> Foo -> Foo"
        shouldEtaConvertTopLevel
            "f (b :: Bool) :: Foo -> Foo = if b then g Foo else h Foo"
          $  "f (b :: Bool) :: Foo -> Foo ="
          ++ "  if b then (\\y -> g Foo y) else h Foo"
  it
      (  "applies under-applied function that is if-expression to minimal"
      ++ "number of missing argument where one branch is lambda expression"
      )
    $ shouldSucceedWith
    $ do
        _ <- defineTestTypeCon "Foo" 0 []
        _ <- defineTestFunc "f" 1 "Bool -> Foo -> Foo"
        _ <- defineTestFunc "g" 2 "Foo -> Foo -> Foo"
        shouldEtaConvertTopLevel
            "f (b :: Bool) :: Foo -> Foo = if b then g Foo else (\\x -> x)"
          $  "f (b :: Bool) :: Foo -> Foo ="
          ++ "  if b then (\\y -> g Foo y) else (\\x -> x)"
  it "works with mutually recursive functions" $ shouldSucceedWith $ do
    _     <- defineTestTypeCon "Foo" 0 []
    _     <- defineTestFunc "k" 0 " Foo -> Foo"
    _     <- defineTestFunc "f" 0 "Foo -> Foo"
    _     <- defineTestFunc "g" 2 "Foo -> Foo -> Foo"
    input <- parseTestModule
      [ "module Test where"
      , "k :: Foo -> Foo = f;"
      , "f :: Foo -> Foo = g (k Foo)"
      ]
    output         <- etaConversionPass input
    expectedOutpyt <- parseTestModule
      [ "module Test where"
      , "k (x :: Foo) :: Foo = f x;"
      , "f (x :: Foo) :: Foo = g (k Foo) x"
      ]
    return (output `shouldBeSimilarTo` expectedOutpyt)

-- | Test group for 'etaConvertExpr' tests.
testEtaConvertExpr :: Spec
testEtaConvertExpr = context "etaConvertExpr" $ do
  it "leaves fully applied functions unchanged" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 0 []
    _ <- defineTestFunc "f" 2 "Foo -> Foo -> Foo"
    "f x y" `shouldEtaConvert` "f x y"
  it "leaves over applied functions unchanged" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 0 []
    _ <- defineTestFunc "f" 2 "Foo -> Foo -> Foo"
    "f x y z" `shouldEtaConvert` "f x y z"
  it "eta-converts under applied functions" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 0 []
    _ <- defineTestFunc "f" 2 "Foo -> Foo -> Foo"
    "f x" `shouldEtaConvert` "\\y -> f x y"
  it "leaves application of local variables unchanged" $ shouldSucceedWith $ do
    shouldEtaConvert "\\(f :: a -> b -> c) x -> f x"
                     "\\(f :: a -> b -> c) x -> f x"
  it "leaves fully applied constructors unchanged" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 0 []
    _ <- defineTestTypeCon "Bar" 0 ["Bar"]
    _ <- defineTestCon "Bar" 2 "Foo -> Foo -> Bar"
    "Bar x y" `shouldEtaConvert` "Bar x y"
  it "leaves over applied functions unchanged" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 0 []
    _ <- defineTestTypeCon "Bar" 0 ["Bar"]
    _ <- defineTestCon "Bar" 2 "Foo -> Foo -> Bar"
    "Bar x y z" `shouldEtaConvert` "Bar x y z"
  it "eta-converts under applied functions" $ shouldSucceedWith $ do
    _ <- defineTestTypeCon "Foo" 0 []
    _ <- defineTestTypeCon "Bar" 0 ["Bar"]
    _ <- defineTestCon "Bar" 2 "Foo -> Foo -> Bar"
    "Bar x" `shouldEtaConvert` "\\y -> Bar x y"
