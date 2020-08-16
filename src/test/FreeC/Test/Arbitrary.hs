{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains @Arbitrary@ instances for IR AST nodes.
module FreeC.Test.Arbitrary where

import           Control.Monad         ( replicateM )
import           Test.QuickCheck

import qualified FreeC.IR.Base.Prelude as IR.Prelude
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax       as IR

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------
-- | Generates an arbitrary type expression.
instance Arbitrary IR.Type where
  arbitrary
    = oneof [ arbitraryTypeVar, arbitraryTypeConApp, arbitraryFuncType ]
   where
     arbitraryTypeVar :: Gen IR.Type
     arbitraryTypeVar = do
       ident <- oneof $ map return [ "a", "b", "c", "d" ]
       return (IR.TypeVar NoSrcSpan ident)

     arbitraryTypeConApp :: Gen IR.Type
     arbitraryTypeConApp = do
       (name, arity) <- oneof $ map return
         [ (IR.Prelude.boolTypeConName, 0)
         , (IR.Prelude.integerTypeConName, 0)
         , (IR.Prelude.unitTypeConName, 0)
         , (IR.Prelude.listTypeConName, 1)
         , (IR.Prelude.tupleTypeConName 2, 2)
         ]
       args <- replicateM arity arbitrary
       return (IR.typeConApp NoSrcSpan name args)

     arbitraryFuncType :: Gen IR.Type
     arbitraryFuncType = IR.FuncType NoSrcSpan <$> arbitrary <*> arbitrary
