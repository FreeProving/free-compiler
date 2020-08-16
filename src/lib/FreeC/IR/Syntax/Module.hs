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
data Module = Module
  { modSrcSpan   :: SrcSpan
  , modName      :: ModName
  , modImports   :: [ ImportDecl ]
  , modTypeDecls :: [ TypeDecl ]
  , modTypeSigs  :: [ TypeSig ]
  , modPragmas   :: [ Pragma ]
  , modFuncDecls :: [ FuncDecl ]
  }
 deriving ( Eq, Show )

-- | Pretty instance for modules.
instance Pretty Module where
  pretty ast = prettyString "module"
    <+> prettyString (modName ast)
    <+> prettyString "where"
    <$$> prettySeparated (semi <> line)
    (map pretty (modImports ast)
     ++ map pretty (modTypeDecls ast)
     ++ map pretty (modTypeSigs ast)
     ++ map pretty (modPragmas ast)
     ++ map pretty (modFuncDecls ast))

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
