-- | This module exports functions for generating Agda that uses the @Free@
--   monad from out intermediate representation.

module FreeC.Backend.Agda.Converter
  ( convertModule
  , convertFuncDecls
  , convertTypeDecls
  )
where

import           FreeC.Backend.Agda.Converter.Module
                                                ( convertModule )
import           FreeC.Backend.Agda.Converter.FuncDecl
                                                ( convertFuncDecls )
import           FreeC.Backend.Agda.Converter.TypeDecl
                                                ( convertTypeDecls )
