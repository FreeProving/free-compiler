-- | This module exports functions for generating Coq that uses the @Free@
--   monad from out intermediate representation.
module FreeC.Backend.Coq.Converter
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
  ) where

import           FreeC.Backend.Coq.Converter.Expr            ( convertExpr )
import           FreeC.Backend.Coq.Converter.FuncDecl
  ( convertFuncComponent, convertFuncDecls )
import           FreeC.Backend.Coq.Converter.FuncDecl.NonRec
  ( convertNonRecFuncDecl )
import           FreeC.Backend.Coq.Converter.FuncDecl.Rec
  ( convertRecFuncDecls )
import           FreeC.Backend.Coq.Converter.Module
  ( convertDecls, convertModule, convertTypeDecls )
import           FreeC.Backend.Coq.Converter.Type
  ( convertType, convertType' )
import           FreeC.Backend.Coq.Converter.TypeDecl
  ( convertDataDecl, convertDataDecls, convertTypeComponent )
