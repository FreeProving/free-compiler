-- | This module contains the definition of comments and pragmas for our
--   intermediate language.

module FreeC.IR.Syntax.Pragma where

import           FreeC.IR.SrcSpan
import           FreeC.IR.Syntax.Name
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Comments                                                                  --
-------------------------------------------------------------------------------

-- | A comment.
--
--   Comments are collected during parsing. However, the final AST
--   contains no comments. Pragmas (see 'DecArgPragma') are extracted
--   from comments by the front end.
data Comment
  = BlockComment { commentSrcSpan :: SrcSpan, commentText :: String }
    -- ^ A multi-line comment (i.e., @{- ... -}@).
  | LineComment { commentSrcSpan :: SrcSpan, commentText :: String }
    -- ^ A single-line comment (i.e., @-- ...@).

-- | Pretty instance for comments.
instance Pretty Comment where
  pretty (BlockComment _ str) =
    prettyString "{-" <> prettyString str <> prettyString "-}"
  pretty (LineComment _ str) = prettyString "--" <> prettyString str

-------------------------------------------------------------------------------
-- Pragmas                                                                   --
-------------------------------------------------------------------------------

-- | All custom pragmas of the compiler start with @HASKELL_TO_COQ@.
customPragmaPrefix :: String
customPragmaPrefix = "HASKELL_TO_COQ"

-- | Data type for custom @{-\# HASKELL_TO_COQ ... \#-}@ pragmas.
data Pragma
  -- | A @{-\# HASKELL_TO_COQ <function> DECREASES ON <argument> \#-}@ or
  --   @{-\# HASKELL_TO_COQ <function> DECREASES ON ARGUMENT <index> \#-}@
  --   pragma.
  = DecArgPragma { pragmaSrcSpan        :: SrcSpan
                 , decArgPragmaFuncName :: QName
                 , decArgPragmaArg      :: Either String Int
                 }
 deriving (Eq, Show)

-- | Pretty instance for custom @{-\# HASKELL_TO_COQ ... \#-}@ pragmas.
instance Pretty Pragma where
  pretty (DecArgPragma _ funcName (Left argName)) = prettyPragma
    (pretty funcName <+> prettyString "DECREASES ON" <+> prettyString argName)
  pretty (DecArgPragma _ funcName (Right argIndex)) = prettyPragma
    (   pretty funcName
    <+> prettyString "DECREASES ON ARGUMENT"
    <+> pretty argIndex
    )

-- | Pretty prints a custom @{-\# HASKELL_TO_COQ ... \#-}@ pragma with the given
--   contents.
prettyPragma :: Doc -> Doc
prettyPragma contents =
  prettyString "{-#"
    <+> prettyString customPragmaPrefix
    <+> contents
    <+> prettyString "#-}"
