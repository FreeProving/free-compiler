-- | This module contains tests for
--   "FreeC.Backend.Coq.Analysis.DecreasingArguments".
module FreeC.Backend.Coq.Analysis.DecreasingArgumentsTests
  ( testDecreasingArguments
  ) where

import           Test.Hspec
  hiding ( shouldReturn )

import           FreeC.Backend.Coq.Analysis.DecreasingArguments
import           FreeC.Environment
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Test.Parser

-- | Test group for 'identifyDecArgs' tests.
testDecreasingArguments :: Spec
testDecreasingArguments
  = describe "FreeC.Backend.Coq.Analysis.DecreasingArguments" $ do
    it "cannot guess decreasing argument of partially applied functions" $ do
      funcDecl <- expectParseTestFuncDecl
        $ "mapRose f r = case r of {"
        ++ "    Rose rs x -> Rose (map (mapRose f) rs) (f x)"
        ++ "  }"
      shouldFail (identifyDecArgs [funcDecl])
    it "guessing decreasing arguments can be bypassed" $ do
      funcName <- expectParseTestQName "mapRose"
      funcDecl <- expectParseTestFuncDecl
        $ "mapRose f r = case r of {"
        ++ "    Rose rs x -> Rose (map (mapRose f) rs) (f x)"
        ++ "  }"
      flip shouldReturn [1] $ do
        modifyEnv $ defineDecArg funcName 1 "r"
        identifyDecArgs [funcDecl]
    it "cannot guess decreasing argument if the argument is not a variable" $ do
      funcDecl <- expectParseTestFuncDecl
        $ "qsort xs = case xs of {"
        ++ "    Nil -> Nil;"
        ++ "    Cons x xs' ->"
        ++ "      append (qsort (filter ((>=) x) xs))"
        ++ "             (Cons x (qsort (filter ((<) x) xs)))"
        ++ "  }"
      shouldFail (identifyDecArgs [funcDecl])
    it "identifies the decreasing argument of simple recursive functions" $ do
      funcDecl <- expectParseTestFuncDecl
        $ "map f xs = case xs of {"
        ++ "    Nil -> Nil;"
        ++ "    Cons x xs' -> Cons (f x) (map f xs')"
        ++ "  }"
      identifyDecArgs [funcDecl] `shouldReturn` [1]
    it "identifies the decreasing argument if there are nested case expressions"
      $ do
        funcDecl <- expectParseTestFuncDecl
          $ "isSubsequenceOf xs ys = case xs of {"
          ++ "    Nil        -> True;"
          ++ "    Cons x xs' -> case ys of {"
          ++ "        Nil        -> False;"
          ++ "        Cons y ys' -> if (==) x y"
          ++ "          then isSubsequenceOf xs' ys'"
          ++ "          else isSubsequenceOf xs ys'"
          ++ "      }"
          ++ "  }"
        identifyDecArgs [funcDecl] `shouldReturn` [1]
    it "allows arbitrarily deep subterms of decreasing argument" $ do
      funcDecl <- expectParseTestFuncDecl
        $ "mod2 n = case n of {"
        ++ "    O   -> O;"
        ++ "    S p -> case p of {"
        ++ "             O   -> S O;"
        ++ "             S q -> mod2 q"
        ++ "           }"
        ++ "  }"
      identifyDecArgs [funcDecl] `shouldReturn` [0]
    it "allows aliases of the decreasing argument" $ do
      funcDecl <- expectParseTestFuncDecl
        $ "tails xs = let { xs0 = xs } in Cons xs0 (case xs0 of {"
        ++ "      Nil        -> Nil;"
        ++ "      Cons x xs' -> tails xs'"
        ++ "    })"
      identifyDecArgs [funcDecl] `shouldReturn` [0]
    it "allows aliases of structurally smaller variables" $ do
      funcDecl <- expectParseTestFuncDecl
        $ "pow2 n = case n of {"
        ++ "    Zero -> Succ Zero;"
        ++ "    Succ n' -> let { n'0 = n' } in add (pow2 n'0) (pow2 n'0)"
        ++ "  }"
      identifyDecArgs [funcDecl] `shouldReturn` [0]
