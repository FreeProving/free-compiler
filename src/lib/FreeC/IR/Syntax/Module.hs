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
-- | A module declaration that contains declarations of type @contents@.
--
--   This type is used for example to represent partially transformed modules
--   where only the name, imports and pragmas of the module are transformed
--   into the intermediate representation.
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
-- | Declarations that can occur on top-level of a 'Module' declaration.
data TopLevelDecl
  = TopLevelTypeDecl { topLevelTypeDecl :: TypeDecl }
  | TopLevelTypeSig { topLevelTypeSig :: TypeSig }
  | TopLevelFuncDecl { topLevelFuncDecl :: FuncDecl }
 deriving ( Eq, Show )

-- | Tests whether the given top-level declaration is a 'TypeDecl'.
isTopLevelTypeDecl :: TopLevelDecl -> Bool
isTopLevelTypeDecl TopLevelTypeDecl {} = True
isTopLevelTypeDecl _                   = False

-- | Tests whether the given top-level declaration is a 'TypeSig'.
isTopLevelTypeSig :: TopLevelDecl -> Bool
isTopLevelTypeSig TopLevelTypeSig {} = True
isTopLevelTypeSig _                  = False

-- | Tests whether the given top-level declaration is a 'FuncDecl'.
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
-- | Gets the type-level declarations of the given module.
modTypeDecls :: Module -> [TypeDecl]
modTypeDecls = map topLevelTypeDecl . filter isTopLevelTypeDecl . modContents

-- | Sets the type-level declarations of the given module.
--
--   All other type-level declarations are discarded.
modWithTypeDecls :: [TypeDecl] -> Module -> Module
modWithTypeDecls decls = modWithContents $ \contents ->
  map TopLevelTypeDecl decls ++ filter (not . isTopLevelTypeDecl) contents

-------------------------------------------------------------------------------
-- Type Signatures                                                           --
-------------------------------------------------------------------------------
-- | Gets the type signatures of the given module.
modTypeSigs :: Module -> [TypeSig]
modTypeSigs = map topLevelTypeSig . filter isTopLevelTypeSig . modContents

-- | Sets the type signatures of the given module.
--
--   All other type signatures are discarded.
modWithTypeSigs :: [TypeSig] -> Module -> Module
modWithTypeSigs decls = modWithContents $ \contents -> map TopLevelTypeSig decls
  ++ filter (not . isTopLevelTypeSig) contents

-------------------------------------------------------------------------------
-- Function Declarations                                                     --
-------------------------------------------------------------------------------
-- | Gets the function declarations of the given module.
modFuncDecls :: Module -> [FuncDecl]
modFuncDecls = map topLevelFuncDecl . filter isTopLevelFuncDecl . modContents

-- | Sets the function declarations of the given module.
--
--   All other function declarations are discarded.
modWithFuncDecls :: [FuncDecl] -> Module -> Module
modWithFuncDecls decls = modWithContents $ \contents ->
  map TopLevelFuncDecl decls ++ filter (not . isTopLevelFuncDecl) contents
