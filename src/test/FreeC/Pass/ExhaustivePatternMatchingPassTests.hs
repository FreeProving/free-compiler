-- name subject to change 

-- | This module contains tests for "FreeC.Pass.EtaConversionPass".

module FreeC.Pass.ExhaustivePatternMatchingPassTests where

import           Test.Hspec

import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Class.Testable
import           FreeC.Pass.ExhaustivePatternMatchingPass
import           FreeC.Test.Environment
import           FreeC.Test.Parser


{-
-------------------------------------------------------------------------------
-- Assumed interface (use for renaming once real interface is known)                                                   --
-------------------------------------------------------------------------------
Pass name : FreeC.Pass.ExhaustivePatternMatchingPass 
Name of function that checks expression: checkCaseExpr 
-}

-------------------------------------------------------------------------------
-- Tests                                                                     --
-------------------------------------------------------------------------------

testExhaustivePatternMatchingPass :: SpecWith ()
testExhaustivePatternMatchingPass = describe "FreeC.Pass.ExhaustivePatternMatchingPass" $ do
    context "Top-level case expressions" $ do
      it "fails when a constructor is missing" $ do 
          input <- expectParseTestExpr  "case (x :: Foobar) of {Foo -> Foo}"
          shouldFail $ do 
           _ <- defineTestTypeCon' "Foobar" 0 [IR.UnQual (IR.Ident "Foo"),
             IR.UnQual (IR.Ident "Bar")]
           _ <- defineTestCon "Foo" 0 "Foobar" 
           _ <- defineTestCon "Bar" 0 "Foobar" 
           _ <- defineTestVar "x" 
           checkCaseExpr input 
      it "fails when a constructor occurs more than once" $ do 
          input <- expectParseTestExpr  
            "case (x :: Foobar) of {Foo -> Foo ; Bar -> Bar ; Foo -> Foo}"
          shouldFail $ do 
           _ <- defineTestTypeCon' "Foobar" 0 [IR.UnQual (IR.Ident "Foo"),
             IR.UnQual (IR.Ident "Bar")]
           _ <- defineTestCon "Foo" 0 "Foobar" 
           _ <- defineTestCon "Bar" 0 "Foobar" 
           _ <- defineTestVar "x" 
           checkCaseExpr input 
      it "succeeds when all constructors occur exactly once" $ do 
          input <- expectParseTestExpr  
            "case (x :: Foobar) of {Foo -> Foo ; Bar -> Bar}"
          shouldSucceed $ do 
           _ <- defineTestTypeCon' "Foobar" 0 [IR.UnQual (IR.Ident "Foo"),
             IR.UnQual (IR.Ident "Bar")]
           _ <- defineTestCon "Foo" 0 "Foobar" 
           _ <- defineTestCon "Bar" 0 "Foobar" 
           _ <- defineTestVar "x" 
           checkCaseExpr input 
      it "fails when a constructor is given too few arguments" $ do 
          input <- expectParseTestExpr  
            "case (x :: Foobar) of {Foo -> Foo ; Bar -> Bar}"
          shouldFail $ do 
           _ <- defineTestTypeCon' "Foobar" 0 [IR.UnQual (IR.Ident "Foo"),
             IR.UnQual (IR.Ident "Bar")]
           _ <- defineTestCon "Foo" 1 "Foobar -> Foobar" 
           _ <- defineTestCon "Bar" 0 "Foobar" 
           _ <- defineTestVar "x" 
           checkCaseExpr input 
      it "fails when a constructor is given too many arguments" $ do 
          input <- expectParseTestExpr  
            "case (x :: Foobar) of {Foo y -> Foo ; Bar y -> Bar}"
          shouldFail $ do 
           _ <- defineTestTypeCon' "Foobar" 0 [IR.UnQual (IR.Ident "Foo"),
             IR.UnQual (IR.Ident "Bar")]
           _ <- defineTestCon "Foo" 1 "Foobar -> Foobar" 
           _ <- defineTestCon "Bar" 0 "Foobar" 
           _ <- defineTestVar "x" 
           checkCaseExpr input 
      it "succeeds when all constructors are given the right number of arguments" $ do 
          input <- expectParseTestExpr  
            "case (x :: Foobar) of {Foo y -> Foo ; Bar y -> Bar}"
          shouldSucceed $ do 
           _ <- defineTestTypeCon' "Foobar" 0 [IR.UnQual (IR.Ident "Foo"),
             IR.UnQual (IR.Ident "Bar")]
           _ <- defineTestCon "Foo" 1 "Foobar -> Foobar" 
           _ <- defineTestCon "Bar" 0 "Foobar" 
           _ <- defineTestVar "x" 
           checkCaseExpr input 
      it "fails when a constructor of the wrong type occurs" $ do 
          input <- expectParseTestExpr  
            "case (x :: Foobar) of {Foo -> Foo ; Bar -> Bar ; Evil -> Bar}"
          shouldFail $ do 
           _ <- defineTestTypeCon' "Foobar" 0 [IR.UnQual (IR.Ident "Foo"),
             IR.UnQual (IR.Ident "Bar")]
           _ <- defineTestTypeCon' "Evil" 0 [IR.UnQual (IR.Ident "Evil")]
           _ <- defineTestCon "Foo" 0 "Foobar" 
           _ <- defineTestCon "Bar" 0 "Foobar" 
           _ <- defineTestCon "Evil" 0 "Evil"
           _ <- defineTestVar "x" 
           checkCaseExpr input 
    context "Nested and deeper case expressions" $ do
      it "fails for a faulty case expression inside an if statement" $ do 
          input <- expectParseTestExpr  "if b then case (x :: Foobar) of {Foo -> Foo} else Bar"
          shouldFail $ do 
           _ <- defineTestTypeCon' "Foobar" 0 [IR.UnQual (IR.Ident "Foo"),
             IR.UnQual (IR.Ident "Bar")]
           _ <- defineTestCon "Foo" 0 "Foobar" 
           _ <- defineTestCon "Bar" 0 "Foobar" 
           _ <- defineTestVar "x" 
           _ <- defineTestVar "b" 
           checkCaseExpr input 
      it "fails for a faulty nested case expression" $ do 
          input <- expectParseTestExpr  "case (x :: Foobar) of {Foo -> case (x :: Foobar) of {Foo -> Foo} ; Bar -> Bar}"
          shouldFail $ do 
           _ <- defineTestTypeCon' "Foobar" 0 [IR.UnQual (IR.Ident "Foo"),
             IR.UnQual (IR.Ident "Bar")]
           _ <- defineTestCon "Foo" 0 "Foobar" 
           _ <- defineTestCon "Bar" 0 "Foobar" 
           _ <- defineTestVar "x" 
           checkCaseExpr input 
      it "fails for a faulty case expression used as another case expression's scrutinee" $ do 
          input <- expectParseTestExpr  "case ((case (x :: Foobar) of {Foo -> x} ) :: Foobar) of {Foo -> Foo ; Bar -> Bar}"
          shouldFail $ do 
           _ <- defineTestTypeCon' "Foobar" 0 [IR.UnQual (IR.Ident "Foo"),
             IR.UnQual (IR.Ident "Bar")]
           _ <- defineTestCon "Foo" 0 "Foobar" 
           _ <- defineTestCon "Bar" 0 "Foobar" 
           _ <- defineTestVar "x" 
           checkCaseExpr input 
      it "succeeds for a valid nested case expression" $ do 
          input <- expectParseTestExpr  "case (x :: Foobar) of {Foo -> case (x :: Foobar) of {Foo -> Foo ; Bar -> Bar} ; Bar -> Bar}"
          shouldSucceed $ do 
           _ <- defineTestTypeCon' "Foobar" 0 [IR.UnQual (IR.Ident "Foo"),
             IR.UnQual (IR.Ident "Bar")]
           _ <- defineTestCon "Foo" 0 "Foobar" 
           _ <- defineTestCon "Bar" 0 "Foobar" 
           _ <- defineTestVar "x" 
           checkCaseExpr input 
           
      it "fails for a faulty case expression inside a lambda" $ do 
          input <- expectParseTestExpr  "\\ y -> case (x :: Foobar) of {Foo -> Foo}"
          shouldFail $ do 
           _ <- defineTestTypeCon' "Foobar" 0 [IR.UnQual (IR.Ident "Foo"),
             IR.UnQual (IR.Ident "Bar")]
           _ <- defineTestCon "Foo" 0 "Foobar" 
           _ <- defineTestVar "x" 
           checkCaseExpr input 
    context "Illegal scrutinee types" $ do
      it "fails if the case expression's scrutinee is a function and alternative list is not empty" $ do 
          input <- expectParseTestExpr  "case f of {Foo -> Foo ; Bar -> Bar}" 
          shouldFail $ do 
           _ <- defineTestTypeCon' "Foobar" 0 [IR.UnQual (IR.Ident "Foo"),
             IR.UnQual (IR.Ident "Bar")]
           _ <- defineTestCon "Foo" 0 "Foobar" 
           _ <- defineTestCon "Bar" 0 "Foobar" 
           _ <- defineTestFunc "f" 1 "Foobar -> Foobar"
           _ <- defineTestVar "b" 
           checkCaseExpr input 
      it "fails if the case expression's scrutinee is a function and alternative list is empty" $ do 
          input <- expectParseTestExpr  "case f of {}" 
          shouldFail $ do 
           _ <- defineTestTypeCon' "Foobar" 0 [IR.UnQual (IR.Ident "Foo"),
             IR.UnQual (IR.Ident "Bar")]
           _ <- defineTestCon "Foo" 0 "Foobar" 
           _ <- defineTestCon "Bar" 0 "Foobar" 
           _ <- defineTestFunc "f" 1 "Foobar -> Foobar"
           _ <- defineTestVar "b" 
           checkCaseExpr input 
      it "succeeds if the case expression's scrutinee is a full function application" $ do 
          input <- expectParseTestExpr  "case (f x :: Foobar) of {Foo -> Foo ; Bar -> Bar}"
          shouldFail $ do 
           _ <- defineTestTypeCon' "Foobar" 0 [IR.UnQual (IR.Ident "Foo"),
             IR.UnQual (IR.Ident "Bar")]
           _ <- defineTestCon "Foo" 0 "Foobar" 
           _ <- defineTestCon "Bar" 0 "Foobar" 
           _ <- defineTestFunc "f" 1 "Foobar -> Foobar"
           _ <- defineTestVar "x" 
           checkCaseExpr input 
      it "fails if the case expression's scrutinee is a lambda" $ do 
          input <- expectParseTestExpr "case (\\ x -> Foo :: Foobar -> Foobar) of {Foo -> Foo ; Bar -> Bar}" 
          shouldFail $ do 
           _ <- defineTestTypeCon' "Foobar" 0 [IR.UnQual (IR.Ident "Foo"),
             IR.UnQual (IR.Ident "Bar")]
           _ <- defineTestCon "Foo" 0 "Foobar" 
           _ <- defineTestCon "Bar" 0 "Foobar" 
           checkCaseExpr input 
      it "fails if the case expression's scrutinee is polymorphic" $ do 
          input <- expectParseTestExpr  "case (x :: a) of {}"
          shouldFail $ do 
           _ <- defineTestTypeCon' "Foobar" 0 [IR.UnQual (IR.Ident "Foo"),
             IR.UnQual (IR.Ident "Bar")]
           _ <- defineTestCon "Foo" 0 "Foobar" 
           _ <- defineTestCon "Bar" 0 "Foobar" 
           _ <- defineTestVar "x" 
           _ <- defineTestTypeVar "a"
           checkCaseExpr input 


        
