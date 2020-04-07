-- | This module contains tests for
--   "FreeC.Backend.Coq.Analysis.ConstantArguments".

module FreeC.Backend.Coq.Analysis.ConstantArgumentsTests
  ( testConstantArguments
  )
where

import qualified Data.Map                      as Map
import           Test.Hspec              hiding ( shouldReturn )

import           FreeC.Backend.Coq.Analysis.ConstantArguments
import qualified FreeC.IR.Syntax               as HS
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Test.Parser

-------------------------------------------------------------------------------
-- Utility functions                                                         --
-------------------------------------------------------------------------------

-- | Like 'identifyConstArgs' but returns just the 'constArgIdents' as a list
--   for each constant argument.
identifyConstArgIdents :: [HS.FuncDecl] -> Converter [[(HS.QName, String)]]
identifyConstArgIdents =
  fmap (map (Map.assocs . constArgIdents)) . identifyConstArgs

-------------------------------------------------------------------------------
-- Test                                                                      --
-------------------------------------------------------------------------------

-- | Test group for @identifyConstArgs@.
testConstantArguments :: Spec
testConstantArguments =
  describe "FreeC.Backend.Coq.Analysis.ConstantArguments" $ do
    it "identifies constant arguments of recursive functions" $ do
      funcDecl <-
        expectParseTestFuncDecl
        $  "map f xs = case xs of {"
        ++ "    Nil        -> Nil;"
        ++ "    Cons x xs' -> Cons (f x) (map f xs')"
        ++ "  }"
      identifyConstArgIdents [funcDecl]
        `shouldReturn` [[(HS.UnQual (HS.Ident "map"), "f")]]

    it "identifies constant arguments of mutually recursive functions" $ do
      funcDecls <- mapM
        expectParseTestFuncDecl
        [ "mapAlt f g xs = case xs of {"
        ++ "    Nil        -> Nil;"
        ++ "    Cons x xs' ->  Cons (f x) (mapAlt' f g xs')"
        ++ "  }"
        , "mapAlt' f g xs = case xs of {"
        ++ "    Nil        -> Nil;"
        ++ "    Cons x xs' -> Cons (g x) (mapAlt f g xs')"
        ++ "  }"
        ]
      identifyConstArgIdents funcDecls
        `shouldReturn` [ [ (HS.UnQual (HS.Ident "mapAlt") , "g")
                         , (HS.UnQual (HS.Ident "mapAlt'"), "g")
                         ]
                       , [ (HS.UnQual (HS.Ident "mapAlt") , "f")
                         , (HS.UnQual (HS.Ident "mapAlt'"), "f")
                         ]
                       ]

    it "does not identify swapped arguments as constant" $ do
      funcDecl <-
        expectParseTestFuncDecl
        $  "mapAlt f g xs = case xs of {"
        ++ "    Nil        -> Nil;"
        ++ "    Cons x xs' -> Cons (f x) (mapAlt g f xs')"
        ++ "  }"
      identifyConstArgIdents [funcDecl] `shouldReturn` []

    it "identifies constant arguments with multiple recursive calls" $ do
      funcDecls <- mapM
        expectParseTestFuncDecl
        [ "foo n xs = case xs of {"
        ++ "    Nil        -> Nil;"
        ++ "    Cons x xs' -> Cons ((+) x n) (bar n xs')"
        ++ "  }"
        , "bar n xs = case xs of {"
        ++ "    Nil        -> Nil;"
        ++ "    Cons x xs' -> Cons ((+) x n) (baz n xs')"
        ++ "  }"
        , "baz n xs = case xs of {"
        ++ "    Nil        -> Nil;"
        ++ "    Cons x xs' -> append (Cons ((+) x n) (foo n xs')) (bar n xs')"
        ++ "  }"
        ]
      identifyConstArgIdents funcDecls
        `shouldReturn` [ [ (HS.UnQual (HS.Ident "bar"), "n")
                         , (HS.UnQual (HS.Ident "baz"), "n")
                         , (HS.UnQual (HS.Ident "foo"), "n")
                         ]
                       ]

    it "does not identify argument as constant if it is modified in one call"
      $ do
          funcDecls <- mapM
            expectParseTestFuncDecl
            [ "foo n xs = case xs of {"
            ++ "    Nil        -> Nil;"
            ++ "    Cons x xs' -> Cons ((+) x n) (bar n xs')"
            ++ "  }"
            , "bar n xs = case xs of {"
            ++ "    Nil        -> Nil;"
            ++ "    Cons x xs' -> Cons ((+) x n) (baz n xs')"
            ++ "  }"
            , "baz n xs = case xs of {"
            ++ "    Nil        -> Nil;"
            ++ "    Cons x xs' ->"
            ++ "      append (Cons ((+) x n) (foo n xs')) (bar ((+) n 1) xs')"
            ++ "  }"
            ]
          identifyConstArgIdents funcDecls `shouldReturn` []
