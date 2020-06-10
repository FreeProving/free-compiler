module FreeC.Backend.Agda.Converter
  ( convertModule
  , convertFuncDecl
  , convertType
  , convertFunctionType
  , convertConstructorType
  , renameAgdaTypeVar
  )
where

import           FreeC.Backend.Agda.Converter.Module
                                                ( convertModule )
import           FreeC.Backend.Agda.Converter.FuncDecl
                                                ( convertFuncDecl )
import           FreeC.Backend.Agda.Converter.Type
                                                ( convertType
                                                , convertFunctionType
                                                , convertConstructorType
                                                , renameAgdaTypeVar
                                                )
