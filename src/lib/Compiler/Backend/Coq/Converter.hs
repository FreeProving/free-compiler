-- | This module exports functions for converting Haskell to Coq using the
--   @Free@ monad.

module Compiler.Backend.Coq.Converter
  ( -- * Modules
    convertModule
  , convertDecls
    -- * Data type declarations
  , convertTypeDecls
  , convertTypeComponent
  , convertDataDecls
  , convertDataDecl
    -- * Function declarations
  , convertFuncDecls
  , convertFuncComponent
  , convertNonRecFuncDecl
  , convertRecFuncDecls
    -- * Type expressions
  , convertType
  , convertType'
   -- * Expressions
  , convertExpr
  )
where

import           Compiler.Backend.Coq.Converter.Expr
                                                ( convertExpr )
import           Compiler.Backend.Coq.Converter.FuncDecl
                                                ( convertFuncDecls
                                                , convertFuncComponent
                                                )
import           Compiler.Backend.Coq.Converter.FuncDecl.NonRec
                                                ( convertNonRecFuncDecl )
import           Compiler.Backend.Coq.Converter.FuncDecl.Rec
                                                ( convertRecFuncDecls )
import           Compiler.Backend.Coq.Converter.Module
                                                ( convertDecls
                                                , convertModule
                                                , convertTypeDecls
                                                )
import           Compiler.Backend.Coq.Converter.Type
                                                ( convertType
                                                , convertType'
                                                )
import           Compiler.Backend.Coq.Converter.TypeDecl
                                                ( convertDataDecl
                                                , convertDataDecls
                                                , convertTypeComponent
                                                )
