-- | This module contains functions for converting Haskell modules to Agda.

module FreeC.Backend.Agda.Converter.Module where

import           Control.Monad                  ( (>=>) )
import           Control.Monad.Extra            ( concatMapM )

import           Data.List.Extra                ( splitOn )
import           Data.Monoid                    ( Ap(Ap)
                                                , getAp
                                                )

import           FreeC.Backend.Agda.Converter.FuncDecl
                                                ( convertFuncDecl )
import           FreeC.Backend.Agda.Converter.TypeDecl
                                                ( convertTypeDecl )
import qualified FreeC.Backend.Agda.Syntax     as Agda
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Pipeline

import           FreeC.Backend.Coq.Converter.Module
                                                ( addDecArgPragma )

-- | Converts a Haskell module to an Agda declaration.
convertModule :: IR.Module -> Converter Agda.Declaration
convertModule = moduleEnv . (runPipeline >=> convertModule')

-- | Like 'convertModule'' but does not apply any compiler passes beforehand.
convertModule' :: IR.Module -> Converter Agda.Declaration
convertModule' modul@(IR.Module _ name _ typeDecls _ _ funcDecls) = do
  mapM_ (addDecArgPragma (IR.modFuncDecls modul)) (IR.modPragmas modul)
  Agda.moduleDecl (convertModName name) <$> getAp (typeDecls' <> funcDecls')
 where
  typeDecls' = Ap $ concatMapM convertTypeDecl typeDecls
  funcDecls' = Ap $ concatMapM convertFuncDecl funcDecls

-- | Converts a Haskell module name to an Agda module name
convertModName :: IR.ModName -> Agda.QName
convertModName name = Agda.qname (init parts) (last parts)
  where parts = Agda.name <$> splitOn "." name
