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
--   A parser for the intermediate language and a description of its syntax
--   can be found in "FreeC.Frontend.IR.Parser". While the intermediate
--   language can be parsed, IR nodes are usually created by parsing another
--   language and converting their AST to the IR AST.
module FreeC.IR.Syntax
  ( module FreeC.IR.Syntax.Expr
  , module FreeC.IR.Syntax.FuncDecl
  , module FreeC.IR.Syntax.Module
  , module FreeC.IR.Syntax.Name
  , module FreeC.IR.Syntax.Pragma
  , module FreeC.IR.Syntax.Type
  , module FreeC.IR.Syntax.TypeDecl
  , module FreeC.IR.Syntax.TypeScheme
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
import           FreeC.IR.Syntax.TypeScheme
import           FreeC.IR.Syntax.TypeVarDecl
