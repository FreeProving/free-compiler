module FreeC.Backend.Agda.Converter
  ( convertModule
  , convertFuncDecl
  , convertTypeDecl
  )
where

import           FreeC.Backend.Agda.Converter.Module
                                                ( convertModule )
import           FreeC.Backend.Agda.Converter.FuncDecl
                                                ( convertFuncDecl )
import           FreeC.Backend.Agda.Converter.TypeDecl
                                                ( convertTypeDecl )
