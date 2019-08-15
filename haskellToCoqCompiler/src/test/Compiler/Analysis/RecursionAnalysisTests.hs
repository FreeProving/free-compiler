module Compiler.Analysis.RecursionAnalysisTests where

import           Test.Hspec

import           Compiler.Analysis.RecursionAnalysis

import           Compiler.Util.Test

-- | Test group for 'identifyDecArgs' tests.
testRecursionAnalysis :: Spec
testRecursionAnalysis = describe "Compiler.Analysis.RecursionAnalysis" $ do
  it "cannot guess decreasing argument of partially applied functions"
    $ shouldReportFatal
    $ fromConverter
    $ do
        (_, _, funcDecls) <- parseTestDecls
          [ -- data Rose a = Rose [Rose a] a
            -- mapRose :: (a -> b) -> Rose a -> Rose b
            unlines
              [ "mapRose f r ="
              , "  case r of"
              , "    (Rose rs x) -> Rose (map (mapRose f) rs) (f x)"
              ]
          ]
        identifyDecArgs funcDecls

  it "cannot guess decreasing argument if the argument is not a variable"
    $ shouldReportFatal
    $ fromConverter
    $ do
        (_, _, funcDecls) <- parseTestDecls
          [ -- qsort :: [a] -> [a]
            unlines
              [ "qsort xs = case xs of"
              , "  [] -> []"
              , "  x : xs' ->"
              , "    qsort (filter (<= x) xs)"
              , "      `append` [x]"
              , "      `append` (qsort (filter (> x) xs))              "
              ]
          ]
        identifyDecArgs funcDecls

  it "identifies the decreasing argument of simple recursive functions"
    $ shouldSucceed
    $ fromConverter
    $ do
        (_, _, funcDecls) <- parseTestDecls
          [ -- map :: (a -> b) -> [a] -> [b]
           "map f xs = case xs of {[] -> []; x : xs' -> f x : map f xs'}"]
        decArgIndecies <- identifyDecArgs funcDecls
        return (decArgIndecies `shouldBe` [1])

  it "identifies the decreasing argument if there are nested case expressions"
    $ shouldSucceed
    $ fromConverter
    $ do
        (_, _, funcDecls) <- parseTestDecls
          [ -- isSubsequenceOf :: [Int] -> [Int] -> Bool
            unlines
              [ "isSubsequenceOf xs ys = case xs of"
              , "  []      -> True"
              , "  x : xs' -> case ys of"
              , "    []      -> False"
              , "    y : ys' -> if x == y"
              , "      then isSubsequenceOf xs' ys'"
              , "      else isSubsequenceOf xs ys'"
              ]
          ]
        decArgIndecies <- identifyDecArgs funcDecls
        return (decArgIndecies `shouldBe` [1])

  it "allows arbitrarily deep subterms of decreasing argument in recursive call"
    $ shouldSucceed
    $ fromConverter
    $ do
        (_, _, funcDecls) <- parseTestDecls
          [ -- data Nat = O | S Nat
            -- mod2 :: Nat -> Nat
            unlines
              [ "mod2 n = case n of"
              , "  O   -> O"
              , "  S p -> case p of"
              , "    O   -> S O"
              , "    S q -> mod2 q"
              ]
          ]
        decArgIndecies <- identifyDecArgs funcDecls
        return (decArgIndecies `shouldBe` [0])
