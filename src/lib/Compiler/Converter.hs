-- | This module exports functions for converting Haskell to Coq using the
--   @Free@ monad.

module Compiler.Converter
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

import           Compiler.Converter.Module      ( convertModule
                                                , convertDecls
                                                , convertFuncDecls
                                                , convertTypeDecls
                                                )
import           Compiler.Converter.Expr        ( convertExpr )
import           Compiler.Converter.FuncDecl    ( convertFuncComponent )
import           Compiler.Converter.FuncDecl.NonRec
                                                ( convertNonRecFuncDecl )
import           Compiler.Converter.FuncDecl.Rec
                                                ( convertRecFuncDecls )
import           Compiler.Converter.Type        ( convertType
                                                , convertType'
                                                )
import           Compiler.Converter.TypeDecl    ( convertTypeComponent
                                                , convertDataDecls
                                                , convertDataDecl
                                                )
