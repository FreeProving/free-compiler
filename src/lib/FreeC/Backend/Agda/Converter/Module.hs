module FreeC.Backend.Agda.Converter.Module where

import           Control.Monad                  ( (>=>) )
import           Control.Monad.Extra            ( concatMapM )

import           Data.List.Extra                ( splitOn )

import           FreeC.Backend.Agda.Converter.FuncDecl
import qualified FreeC.Backend.Agda.Syntax     as Agda
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Pipeline


-- | Converts a Haskell module to an Agda declaration.
convertModule :: IR.Module -> Converter Agda.Declaration
convertModule = moduleEnv . (runPipeline >=> convertModule')

-- | Like 'convertModule'' but does not apply any compiler passes beforehand.
convertModule' :: IR.Module -> Converter Agda.Declaration
convertModule' (IR.Module _ name _ _ _ _ funcDecls) =
  Agda.moduleDecl (convertModName name) <$> concatMapM convertFuncDecl funcDecls

convertModName :: IR.ModName -> Agda.QName
convertModName name = Agda.qname (init parts) (last parts)
  where parts = Agda.name <$> splitOn "." name
