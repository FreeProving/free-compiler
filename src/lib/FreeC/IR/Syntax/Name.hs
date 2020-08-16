-- | This module contains the definition of names of our intermediate language.
module FreeC.IR.Syntax.Name where

import           FreeC.IR.SrcSpan
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Unqualifiable names                                                       --
-------------------------------------------------------------------------------
-- | An identifier or a symbolic name.
--
--   The constructors of this type do not contain source spans because
--   'Name's are intended to be comparable. They are used as keys to
--   identify nodes of the dependency graph for example.
data Name
  = Ident String     -- ^ An identifier, e.g. @Ident \"f\"@ for a function @f@.
  | Symbol String    -- ^ A symbolic name, e.g. @Symbol \"+\"@ for @(+)@.
 deriving ( Eq, Ord, Show )

-- | Extracts an identifier from a name. Returns @Nothing@ if the
--   given name is a symbol and not an identifier.
identFromName :: Name -> Maybe String
identFromName (Ident ident) = Just ident
identFromName (Symbol _)    = Nothing

-- | Pretty instance for identifiers and symbols.
instance Pretty Name where
  pretty (Ident ident)   = prettyString ident
  pretty (Symbol symbol) = parens (prettyString symbol)

  prettyList = prettySeparated (comma <> space) . map pretty

-------------------------------------------------------------------------------
-- Qualifiable names                                                         --
-------------------------------------------------------------------------------
-- | A qualifiable 'Name'.
data QName
  = Qual ModName Name -- ^ A qualified 'Name'.
  | UnQual Name       -- ^ An unqualified 'Name'.
 deriving ( Eq, Ord, Show )

-- | Extracts the name of a qualifiable name.
nameFromQName :: QName -> Name
nameFromQName (UnQual name) = name
nameFromQName (Qual _ name) = name

-- | Extracts an identifier from a qualifiable name.
identFromQName :: QName -> Maybe String
identFromQName = identFromName . nameFromQName

-- | Converts a qualifiable name to a name that is qualified with
--   the given module name.
toQual :: ModName -> QName -> QName
toQual modName' = Qual modName' . nameFromQName

-- | Converts a qualifiable name to an unqualified name.
toUnQual :: QName -> QName
toUnQual = UnQual . nameFromQName

-- | Pretty instance for qualifiable identifiers and symbols.
instance Pretty QName where
  pretty (Qual modId name)
    | null modId = pretty name
    | otherwise = prettyString modId <> dot <> pretty name
  pretty (UnQual name)     = pretty name

  prettyList = prettySeparated (comma <> space) . map pretty

-------------------------------------------------------------------------------
-- Name spaces                                                               --
-------------------------------------------------------------------------------
-- | Data type for the different name spaces of the intermediate representation.
--
--   Similar to Haskell, type and function names live in separate name spaces.
--
--   Additionally, there is a name space for fresh identifiers without a
--   corresponding IR node. If a fresh identifier is introduced and used
--   as an IR variable or type variable name, the corresponding entry
--   lives in the value or type scope respectively. The 'FreshScope'
--   contains only IR identifiers that were generated such that their
--   renamed counterpart of the target language can be used as a fresh
--   identifier by the back end.
data Scope = TypeScope | ValueScope | FreshScope
 deriving ( Eq, Ord, Show )

-- | A 'QName' with additional information about its name space.
type ScopedName = (Scope, QName)

-------------------------------------------------------------------------------
-- Aliases for name types                                                    --
-------------------------------------------------------------------------------
-- | The name of a type variable.
type TypeVarIdent = String

-- | The name of a module.
type ModName = String

-- | The name of a function or built-in operator used in prefix notation, e.g.
--   @f x y@ or @(+) n m@
type VarName = QName

-- | The name of a constructor used in prefix notation, e.g. @(:) x xs@.
type ConName = QName

-- | The name of a type or type constructor, e.g. @Integer@ or @[] a@
type TypeConName = QName

-------------------------------------------------------------------------------
-- Names of top-level declarations                                           --
-------------------------------------------------------------------------------
-- | The name of a top-level declaration including location information.
data DeclIdent
  = DeclIdent { declIdentSrcSpan :: SrcSpan, declIdentName :: QName }
 deriving ( Eq, Show )

-- | Pretty instance for names of declarations.
instance Pretty DeclIdent where
  pretty     = pretty . declIdentName

  prettyList = prettySeparated (comma <> space) . map pretty

-------------------------------------------------------------------------------
-- Internal identifiers                                                      --
-------------------------------------------------------------------------------
-- | The character that is used to mark internal identifiers.
--
--   This is used to generate fresh identifiers that don't conflict with user-
--   defined identifiers.
internalIdentChar :: Char
internalIdentChar = '@'

-- | Tests whether the given identifier was generated for internal use only
--   (i.e., contains 'internalIdentChar').
isInternalIdent :: String -> Bool
isInternalIdent = elem internalIdentChar

-- | Tests whether the given name was generated for internal use only (i.e.,
--   it is an identifier that matches 'isInternalIdent').
isInternalName :: Name -> Bool
isInternalName (Ident ident) = isInternalIdent ident
isInternalName (Symbol _)    = False

-- | Tests whether the given qualifiable name was generated for internal use
--   only (i.e., the qualified name is internal according to 'isInternalName').
isInternalQName :: QName -> Bool
isInternalQName (UnQual name) = isInternalName name
isInternalQName (Qual _ name) = isInternalName name
