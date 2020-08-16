-- | This module contains functions for converting Haskell modules to Agda.
module FreeC.Backend.Agda.Converter.Module where

import           Control.Monad.Extra                   ( concatMapM )
import           Data.List.Extra                       ( splitOn )
import           Data.Monoid                           ( Ap(Ap), getAp )

import qualified FreeC.Backend.Agda.Base               as Agda.Base
import           FreeC.Backend.Agda.Converter.FuncDecl ( convertFuncDecls )
import           FreeC.Backend.Agda.Converter.TypeDecl ( convertTypeDecls )
import qualified FreeC.Backend.Agda.Syntax             as Agda
import           FreeC.Environment                     ( lookupAvailableModule )
import           FreeC.Environment.ModuleInterface     ( interfaceAgdaLibName )
import           FreeC.IR.DependencyGraph
  ( groupFuncDecls, groupTypeDecls )
import           FreeC.IR.Pragma
import qualified FreeC.IR.Syntax                       as IR
import           FreeC.Monad.Converter

-- | Converts an IR module to an Agda declaration.
convertModule :: IR.Module -> Converter Agda.Declaration
convertModule (IR.Module _ name importDecls typeDecls _ modPragmas funcDecls)
  = do
    mapM_ (addDecArgPragma funcDecls) modPragmas
    Agda.moduleDecl (convertModName name) <$> getAp
      (importDecls' <> typeDecls' <> funcDecls')
 where
   importDecls' = Ap $ convertImportDecls importDecls

   typeDecls'   = Ap $ concatMapM convertTypeDecls $ groupTypeDecls typeDecls

   funcDecls'   = Ap $ concatMapM convertFuncDecls $ groupFuncDecls funcDecls

-- | Converts an IR module name to an Agda module name.
convertModName :: IR.ModName -> Agda.QName
convertModName name = Agda.qname (init parts) (last parts)
 where
   parts = Agda.name <$> splitOn "." name

-------------------------------------------------------------------------------
-- Import declarations                                                       --
-------------------------------------------------------------------------------
-- | Converts the given import declarations to Agda.
convertImportDecls :: [ IR.ImportDecl ] -> Converter [ Agda.Declaration ]
convertImportDecls imports = (Agda.Base.imports ++)
  <$> mapM convertImportDecl imports

-- | Convert an import declaration.
convertImportDecl :: IR.ImportDecl -> Converter Agda.Declaration
convertImportDecl (IR.ImportDecl _ modName) = do
  Just iface <- inEnv $ lookupAvailableModule modName
  return $ Agda.simpleImport $ Agda.qname [interfaceAgdaLibName iface]
    $ Agda.name modName
