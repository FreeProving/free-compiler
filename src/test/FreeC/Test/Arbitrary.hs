{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains @Arbitrary@ instances for IR AST nodes.

module FreeC.Test.Arbitrary where

import           Control.Monad                  ( replicateM )
import           Test.QuickCheck

import qualified FreeC.IR.Base.Prelude         as HS.Prelude
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax               as HS

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------

-- | Generates an arbitrary type expression.
instance Arbitrary HS.Type where
  arbitrary = oneof [arbitraryTypeVar, arbitraryTypeConApp, arbitraryFuncType]
   where
    arbitraryTypeVar :: Gen HS.Type
    arbitraryTypeVar = do
      ident <- oneof $ map return ["a", "b", "c", "d"]
      return (HS.TypeVar NoSrcSpan ident)

    arbitraryTypeConApp :: Gen HS.Type
    arbitraryTypeConApp = do
      (name, arity) <- oneof $ map
        return
        [ (HS.Prelude.boolTypeConName   , 0)
        , (HS.Prelude.integerTypeConName, 0)
        , (HS.Prelude.unitTypeConName   , 0)
        , (HS.Prelude.listTypeConName   , 1)
        , (HS.Prelude.tupleTypeConName 2, 2)
        ]
      args <- replicateM arity arbitrary
      return (HS.typeConApp NoSrcSpan name args)

    arbitraryFuncType :: Gen HS.Type
    arbitraryFuncType = HS.FuncType NoSrcSpan <$> arbitrary <*> arbitrary
