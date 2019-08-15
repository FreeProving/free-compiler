-- | This module exports functions for converting Haskell to Coq using the
--   @Free@ monad.

module Compiler.Converter
  ( -- * Modules
    convertModule
  , convertModuleWithPreamble
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
                                                , convertModuleWithPreamble
                                                , convertDecls
                                                , convertFuncDecls
                                                , convertTypeDecls
                                                )
import           Compiler.Converter.Expr        ( convertExpr )
import           Compiler.Converter.FuncDecl    ( convertFuncComponent
                                                , convertNonRecFuncDecl
                                                , convertRecFuncDecls
                                                )
import           Compiler.Converter.Type        ( convertType
                                                , convertType'
                                                )
import           Compiler.Converter.TypeDecl    ( convertTypeComponent
                                                , convertDataDecls
                                                , convertDataDecl
                                                )
