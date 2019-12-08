module Compiler.Analysis.RecursionAnalysisTests where

import qualified Data.Map.Strict               as Map
import           Test.Hspec

import           Compiler.Analysis.RecursionAnalysis

import           Compiler.Util.Test

-- | Test group for recursion analysis tests.
testRecursionAnalysis :: Spec
testRecursionAnalysis = describe "Compiler.Analysis.RecursionAnalysis" $ do
  testIdentifyDecArgs
  testIdentifyConstArgs

-- | Test group for 'identifyDecArgs' tests.
testIdentifyDecArgs :: Spec
testIdentifyDecArgs = do
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
          [ -- isSubsequenceOf :: [Integer] -> [Integer] -> Bool
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

-- | Test group for @identifyConstArgs@.
testIdentifyConstArgs :: Spec
testIdentifyConstArgs = do
  it "identifies constant arguments of recursive functions"
    $ shouldSucceed
    $ fromConverter
    $ do
        (_, _, funcDecls) <- parseTestDecls
          [ -- map :: (a -> b) -> [a] -> [b]
            unlines
              [ "map f xs = case xs of"
              , "  []      -> [];"
              , "  x : xs' -> f x : map f xs'"
              ]
          ]
        identMaps <- map (Map.assocs . constArgIdents)
          <$> identifyConstArgs funcDecls
        return (identMaps `shouldBe` [[("map", "f")]])
  it "identifies constant arguments of mutually recursive functions"
    $ shouldSucceed
    $ fromConverter
    $ do
        (_, _, funcDecls) <- parseTestDecls
          [ -- mapAlt :: (a -> b) -> (a -> b) -> [a] -> [b]
            unlines
            [ "mapAlt f g xs = case xs of"
            , "  []      -> [];"
            , "  x : xs' -> f x : mapAlt' f g xs'"
            ]
            -- mapAlt' :: (a -> b) -> (a -> b) -> [a] -> [b]
          , unlines
            [ "mapAlt' f g xs = case xs of"
            , "  []      -> [];"
            , "  x : xs' -> g x : mapAlt f g xs'"
            ]
          ]
        identMaps <- map (Map.assocs . constArgIdents)
          <$> identifyConstArgs funcDecls
        return
          (          identMaps
          `shouldBe` [ [("mapAlt", "g"), ("mapAlt'", "g")]
                     , [("mapAlt", "f"), ("mapAlt'", "f")]
                     ]
          )
  it "does not identify swapped arguments as constant"
    $ shouldSucceed
    $ fromConverter
    $ do
        (_, _, funcDecls) <- parseTestDecls
          [ -- mapAlt :: (a -> b) -> (a -> b) -> [a] -> [b]
            unlines
              [ "mapAlt f g xs = case xs of"
              , "  []      -> []"
              , "  x : xs' -> f x : mapAlt g f xs'"
              ]
          ]
        identMaps <- map (Map.assocs . constArgIdents)
          <$> identifyConstArgs funcDecls
        return (identMaps `shouldBe` [])
  it "identifies constant arguments with multiple recursive calls"
    $ shouldSucceed
    $ fromConverter
    $ do
        (_, _, funcDecls) <- parseTestDecls
          [ -- foo :: Integer -> [Integer] -> [Integer]
            unlines
            [ "foo n xs = case xs of"
            , "    []      -> []"
            , "    x : xs' -> (x + n) : bar n xs'"
            ]
          ,  -- bar :: Integer -> [Integer] -> [Integer]
            unlines
            [ "bar n xs = case xs of"
            , "    []      -> []"
            , "    x : xs' -> (x + n) : baz n xs'"
            ]
          ,  -- baz :: Integer -> [Integer] -> [Integer]
            unlines
            [ "baz n xs = case xs of"
            , "    []      -> []"
            , "    x : xs' -> (x + n) : foo n xs' `append` bar n xs'"
            ]
          ]
        identMaps <- map (Map.assocs . constArgIdents)
          <$> identifyConstArgs funcDecls
        return
          (identMaps `shouldBe` [[("bar", "n"), ("baz", "n"), ("foo", "n")]])
  it "does not identify argument as constant if it is modified in one call"
    $ shouldSucceed
    $ fromConverter
    $ do
        (_, _, funcDecls) <- parseTestDecls
          [ -- foo :: Integer -> [Integer] -> [Integer]
            unlines
            [ "foo n xs = case xs of"
            , "    []      -> []"
            , "    x : xs' -> (x + n) : bar n xs'"
            ]
          ,  -- bar :: Integer -> [Integer] -> [Integer]
            unlines
            [ "bar n xs = case xs of"
            , "    []      -> []"
            , "    x : xs' -> (x + n) : baz n xs'"
            ]
          ,  -- baz :: Integer -> [Integer] -> [Integer]
            unlines
            [ "baz n xs = case xs of"
            , "    []      -> []"
            , "    x : xs' -> (x + n) : foo n xs' `append` bar (n + 1) xs'"
            ]
          ]
        identMaps <- map (Map.assocs . constArgIdents)
          <$> identifyConstArgs funcDecls
        return (identMaps `shouldBe` [])
