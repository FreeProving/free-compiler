-- | This module contains the abstract syntax tree (AST) for the intermediate
--   representation (IR) of the compiler.
--
--   The intermediate language is very similar to the subset of Haskell
--   supported by the compiler. The main goal is to make the transformations
--   on the AST and code generation functions easier to comprehend. The IR does
--   have fewer syntactic constructs than  Haskell AST that fewer cases need to
--   be distinguished. For example, there is no explicit representation of
--   infix function applications and no list literals. These kinds of syntactic
--   sugar must be removed by the front end.
--
--   An additional goal of this AST is to reduce coupling with the parsing
--   library and source language. Ideally the compiler works with any language
--   whose AST can be transformed into this intermediate representation.
--
--   At the moment there is no parser for this AST. Instances of the AST are
---  usually created by converting an existing AST (e.g. a Haskell AST from
--   the @haskell-src-ext@ package). However, the AST can be pretty printed.
--   It's syntax is based on Haskell's syntax.
module FreeC.IR.Syntax
  ( module FreeC.IR.Syntax.Expr
  , module FreeC.IR.Syntax.FuncDecl
  , module FreeC.IR.Syntax.Module
  , module FreeC.IR.Syntax.Name
  , module FreeC.IR.Syntax.Pragma
  , module FreeC.IR.Syntax.Type
  , module FreeC.IR.Syntax.TypeDecl
  , module FreeC.IR.Syntax.TypeSchema
  , module FreeC.IR.Syntax.TypeVarDecl
  )
where

import           FreeC.IR.Syntax.Expr
import           FreeC.IR.Syntax.FuncDecl
import           FreeC.IR.Syntax.Module
import           FreeC.IR.Syntax.Name
import           FreeC.IR.Syntax.Pragma
import           FreeC.IR.Syntax.Type
import           FreeC.IR.Syntax.TypeDecl
import           FreeC.IR.Syntax.TypeSchema
import           FreeC.IR.Syntax.TypeVarDecl
