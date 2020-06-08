module FreeC.Backend.Agda.Converter.Module where

import           Control.Monad                  ( (>=>) )

import qualified FreeC.Backend.Agda.Syntax     as Agda
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Pipeline


-- | Converts a Haskell module to an Agda declaration.
convertModule :: IR.Module -> Converter [Agda.Declaration]
convertModule = moduleEnv . (runPipeline >=> convertModule')

-- | Like 'convertModule'' but does not apply any compiler passes beforehand.
convertModule' :: IR.Module -> Converter [Agda.Declaration]
convertModule' _ = undefined
