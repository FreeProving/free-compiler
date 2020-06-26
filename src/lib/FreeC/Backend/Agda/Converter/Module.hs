-- | This module contains functions for converting Haskell modules to Agda.

module FreeC.Backend.Agda.Converter.Module where

import           Control.Monad                  ( (>=>) )
import           Control.Monad.Extra            ( concatMapM )

import           Data.List.Extra                ( splitOn )
import           Data.Monoid                    ( Ap(Ap)
                                                , getAp
                                                )

import           FreeC.Backend.Agda.Converter.FuncDecl
                                                ( convertFuncDecls )
import           FreeC.Backend.Agda.Converter.TypeDecl
                                                ( convertTypeDecls )
import qualified FreeC.Backend.Agda.Syntax     as Agda
import           FreeC.IR.DependencyGraph       ( groupTypeDecls
                                                , groupFuncDecls
                                                )
import           FreeC.IR.Pragma
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Pipeline

-- | Converts a Haskell module to an Agda declaration.
convertModule :: IR.Module -> Converter Agda.Declaration
convertModule = moduleEnv . (runPipeline >=> convertModule')

-- | Like 'convertModule'' but does not apply any compiler passes beforehand.
convertModule' :: IR.Module -> Converter Agda.Declaration
convertModule' modul@(IR.Module _ name _ typeDecls _ _ funcDecls) = do
  mapM_ (addDecArgPragma (IR.modFuncDecls modul)) (IR.modPragmas modul)
  Agda.moduleDecl (convertModName name) <$> getAp (typeDecls' <> funcDecls')
 where
  typeDecls' = Ap $ concatMapM convertTypeDecls $ groupTypeDecls typeDecls
  funcDecls' = Ap $ concatMapM convertFuncDecls $ groupFuncDecls funcDecls

-- | Converts a Haskell module name to an Agda module name
convertModName :: IR.ModName -> Agda.QName
convertModName name = Agda.qname (init parts) (last parts)
  where parts = Agda.name <$> splitOn "." name
