module FreeC.Analysis.RecursionAnalysisTests where

import qualified Data.Map.Strict               as Map
import           Test.Hspec

import           FreeC.Analysis.RecursionAnalysis
import           FreeC.Backend.Coq.Converter.Module
                                                ( addDecArgPragma )
import           FreeC.IR.Syntax               as HS

import           FreeC.Util.Test

-- | Test group for recursion analysis tests.
testRecursionAnalysis :: Spec
testRecursionAnalysis = describe "FreeC.Analysis.RecursionAnalysis" $ do
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

  it "allows the decreasing argument's name to be annotated using pragmas"
    $ shouldSucceed
    $ fromConverter
    $ do
        ast <- parseTestModule
          [ "data Rose a = Rose [Rose a] a"
          , "{-# HASKELL_TO_COQ mapRose DECREASES ON r #-}"
          , "mapRose :: (a -> b) -> Rose a -> Rose b"
          , "mapRose f r ="
          , "  case r of"
          , "    (Rose rs x) -> Rose (map (mapRose f) rs) (f x)"
          ]
        let funcDecls = HS.modFuncDecls ast
            pragmas   = HS.modPragmas ast
        mapM_ (addDecArgPragma funcDecls) pragmas
        _ <- identifyDecArgs funcDecls
        return (return ())

  it "allows the decreasing argument's index to be annotated using pragmas"
    $ shouldSucceed
    $ fromConverter
    $ do
        ast <- parseTestModule
          [ "data Rose a = Rose [Rose a] a"
          , "{-# HASKELL_TO_COQ mapRose DECREASES ON ARGUMENT 2 #-}"
          , "mapRose :: (a -> b) -> Rose a -> Rose b"
          , "mapRose f r ="
          , "  case r of"
          , "    (Rose rs x) -> Rose (map (mapRose f) rs) (f x)"
          ]
        let funcDecls = HS.modFuncDecls ast
            pragmas   = HS.modPragmas ast
        mapM_ (addDecArgPragma funcDecls) pragmas
        _ <- identifyDecArgs funcDecls
        return (return ())

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
        return (identMaps `shouldBe` [[(HS.UnQual (HS.Ident "map"), "f")]])
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
          `shouldBe` [ [ (HS.UnQual (HS.Ident "mapAlt") , "g")
                       , (HS.UnQual (HS.Ident "mapAlt'"), "g")
                       ]
                     , [ (HS.UnQual (HS.Ident "mapAlt") , "f")
                       , (HS.UnQual (HS.Ident "mapAlt'"), "f")
                       ]
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
          (          identMaps
          `shouldBe` [ [ (HS.UnQual (HS.Ident "bar"), "n")
                       , (HS.UnQual (HS.Ident "baz"), "n")
                       , (HS.UnQual (HS.Ident "foo"), "n")
                       ]
                     ]
          )
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
