{-# LANGUAGE FlexibleInstances #-}

-- | This module contains the definition of modules of our intermediate
--   language.
module FreeC.IR.Syntax.Module where

import           FreeC.IR.SrcSpan
import           FreeC.IR.Syntax.FuncDecl
import           FreeC.IR.Syntax.Name
import           FreeC.IR.Syntax.Pragma
import           FreeC.IR.Syntax.TypeDecl
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------
-- | A module declaration.
data ModuleOf contents = ModuleOf
  { modSrcSpan  :: SrcSpan
  , modName     :: ModName
  , modImports  :: [ImportDecl]
  , modPragmas  :: [Pragma]
  , modContents :: contents
  }
 deriving ( Eq, Show )

-- | Applies the given function to the contents of the given module.
modWithContents
  :: (contents -> contents') -> ModuleOf contents -> ModuleOf contents'
modWithContents f ast = ast { modContents = f (modContents ast) }

-- | A module declaration.
type Module = ModuleOf [TopLevelDecl]

-- | Pretty instance for modules.
instance Pretty contents => Pretty (ModuleOf [contents]) where
  pretty ast = prettyString "module"
    <+> prettyString (modName ast)
    <+> prettyString "where"
    <$$> prettySeparated (semi <> line) (map pretty (modContents ast))

-------------------------------------------------------------------------------
-- Imports                                                                   --
-------------------------------------------------------------------------------
-- | An import declaration.
data ImportDecl
  = ImportDecl { importSrcSpan :: SrcSpan, importName :: ModName }
 deriving ( Eq, Show )

-- | Pretty instance for import declarations.
instance Pretty ImportDecl where
  pretty decl = prettyString "import" <+> prettyString (importName decl)

-------------------------------------------------------------------------------
-- Declarations                                                              --
-------------------------------------------------------------------------------
data TopLevelDecl
  = TopLevelTypeDecl { topLevelTypeDecl :: TypeDecl }
  | TopLevelTypeSig { topLevelTypeSig :: TypeSig }
  | TopLevelFuncDecl { topLevelFuncDecl :: FuncDecl }
 deriving ( Eq, Show )

isTopLevelTypeDecl :: TopLevelDecl -> Bool
isTopLevelTypeDecl TopLevelTypeDecl {} = True
isTopLevelTypeDecl _                   = False

isTopLevelTypeSig :: TopLevelDecl -> Bool
isTopLevelTypeSig TopLevelTypeSig {} = True
isTopLevelTypeSig _                  = False

isTopLevelFuncDecl :: TopLevelDecl -> Bool
isTopLevelFuncDecl TopLevelFuncDecl {} = True
isTopLevelFuncDecl _                   = False

-- | Pretty instance for top-level declarations.
instance Pretty TopLevelDecl where
  pretty (TopLevelTypeDecl typeDecl) = pretty typeDecl
  pretty (TopLevelTypeSig typeSig)   = pretty typeSig
  pretty (TopLevelFuncDecl funcDecl) = pretty funcDecl

-------------------------------------------------------------------------------
-- Type Declarations                                                         --
-------------------------------------------------------------------------------
modTypeDecls :: Module -> [TypeDecl]
modTypeDecls = map topLevelTypeDecl . filter isTopLevelTypeDecl . modContents

modWithTypeDecls :: [TypeDecl] -> Module -> Module
modWithTypeDecls decls = modWithContents $ \contents ->
  map TopLevelTypeDecl decls ++ filter (not . isTopLevelTypeDecl) contents

-------------------------------------------------------------------------------
-- Type Signatures                                                           --
-------------------------------------------------------------------------------
modTypeSigs :: Module -> [TypeSig]
modTypeSigs = map topLevelTypeSig . filter isTopLevelTypeSig . modContents

modWithTypeSigs :: [TypeSig] -> Module -> Module
modWithTypeSigs decls = modWithContents $ \contents -> map TopLevelTypeSig decls
  ++ filter (not . isTopLevelTypeSig) contents

-------------------------------------------------------------------------------
-- Function Declarations                                                     --
-------------------------------------------------------------------------------
modFuncDecls :: Module -> [FuncDecl]
modFuncDecls = map topLevelFuncDecl . filter isTopLevelFuncDecl . modContents

modWithFuncDecls :: [FuncDecl] -> Module -> Module
modWithFuncDecls decls = modWithContents $ \contents ->
  map TopLevelFuncDecl decls ++ filter (not . isTopLevelFuncDecl) contents
