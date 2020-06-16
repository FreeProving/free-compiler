module FreeC.Backend.Agda.Analysis.RecursiveDataType
  ( isRecursiveDataType
  )
where

import qualified FreeC.IR.Syntax               as IR

isRecursiveDataType :: IR.TypeDecl -> Bool
isRecursiveDataType (IR.TypeSynDecl _ _ _ _) = False
isRecursiveDataType (IR.DataDecl _ ident _ constructors) =
  or $ map (requires ident) constructors

requires :: IR.DeclIdent -> IR.ConDecl -> Bool
requires ident (IR.ConDecl _ _ argTypes) = or $ map (contains ident) argTypes

contains :: IR.DeclIdent -> IR.Type -> Bool
contains (IR.DeclIdent _ _) (IR.TypeVar _ _) = False
contains (IR.DeclIdent _ dataName) (IR.TypeCon _ conName) = dataName == conName
contains ident (IR.TypeApp _ l r) = contains ident l || contains ident r
contains ident (IR.FuncType _ l r) = contains ident l || contains ident r

