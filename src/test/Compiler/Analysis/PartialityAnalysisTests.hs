module Compiler.Analysis.PartialityAnalysisTests where

import           Test.Hspec

import           Compiler.Analysis.DependencyGraph
import           Compiler.Analysis.PartialityAnalysis
import           Compiler.Haskell.AST          as HS

import           Compiler.Util.Test

-- | Test group for 'identifyPartialFuncs' tests.
testPartialityAnalysis :: Spec
testPartialityAnalysis = describe "Compiler.Analysis.PartialityAnalysis" $ do
  it "recognizes directly partial functions using 'undefined'"
    $ shouldSucceed
    $ fromConverter
    $ do
        (_, _, funcDecls) <- parseTestDecls
          [ "head :: [a] -> a"
          , "head xs = case xs of { [] -> undefined; x : xs' -> x }"
          ]
        return
          (identifyPartialFuncs [] (funcDependencyGraph funcDecls)
          `shouldContain` [HS.Ident "head"]
          )

  it "recognizes indirectly partial functions using 'undefined'"
    $ shouldSucceed
    $ fromConverter
    $ do
        (_, _, funcDecls) <- parseTestDecls
          [ "head :: [a] -> a"
          , "head xs = case xs of { [] -> undefined; x : xs' -> x }"
          , "heads :: [[a]] -> [a]"
          , "heads = map head"
          ]
        return
          (identifyPartialFuncs [] (funcDependencyGraph funcDecls)
          `shouldContain` [HS.Ident "heads"]
          )

  it "recognizes directly partial functions using 'error'"
    $ shouldSucceed
    $ fromConverter
    $ do
        (_, _, funcDecls) <- parseTestDecls
          [ "head :: [a] -> a"
          , "head xs = case xs of {"
          ++ "  []      -> error \"head: empty list\";"
          ++ "  x : xs' -> x"
          ++ "}"
          ]
        return
          (identifyPartialFuncs [] (funcDependencyGraph funcDecls)
          `shouldContain` [HS.Ident "head"]
          )

  it "recognizes indirectly partial functions using 'error'"
    $ shouldSucceed
    $ fromConverter
    $ do
        (_, _, funcDecls) <- parseTestDecls
          [ "head :: [a] -> a"
          , "head xs = case xs of {"
          ++ "  []      -> error \"head: empty list\";"
          ++ "  x : xs' -> x"
          ++ "}"
          , "heads :: [[a]] -> [a]"
          , "heads = map head"
          ]
        return
          (identifyPartialFuncs [] (funcDependencyGraph funcDecls)
          `shouldContain` [HS.Ident "heads"]
          )
