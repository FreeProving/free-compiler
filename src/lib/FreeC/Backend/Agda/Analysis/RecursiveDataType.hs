-- | This module contains functions for analysing data declarations. The goal is
--   to decide if a data type is recursive.
module FreeC.Backend.Agda.Analysis.RecursiveDataType
  ( isRecursiveDataType
  )
where

import qualified FreeC.IR.Syntax               as IR

-- | Do the values of the data type contain other values from the type?
isRecursiveDataType :: IR.TypeDecl -> Bool
isRecursiveDataType (IR.TypeSynDecl _ _ _ _) = False
isRecursiveDataType (IR.DataDecl _ ident _ constructors) =
  any (requires ident) constructors

-- | Does the constructor use a type constructor with the given name?
requires :: IR.DeclIdent -> IR.ConDecl -> Bool
requires ident (IR.ConDecl _ _ argTypes) = any (contains ident) argTypes

-- | Does the given type contain a type constructor with the given name?
contains :: IR.DeclIdent -> IR.Type -> Bool
contains (IR.DeclIdent _ _) (IR.TypeVar _ _) = False
contains (IR.DeclIdent _ dataName) (IR.TypeCon _ conName) = dataName == conName
contains ident (IR.TypeApp _ l r) = contains ident l || contains ident r
contains ident (IR.FuncType _ l r) = contains ident l || contains ident r

