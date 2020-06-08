module FreeC.Backend.Agda.Converter.FuncDecl where

import qualified FreeC.Backend.Agda.Syntax     as Agda
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter

convertFuncDecl :: IR.FuncDecl -> Converter [Agda.Declaration]
convertFuncDecl _ = pure []
