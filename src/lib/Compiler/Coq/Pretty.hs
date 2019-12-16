-- | This module contains a 'Pretty' instance for nodes of the Coq AST.
--
--   Since we want to have a pretty instance for all 'Gallina' instances
--   but want to avoid overlapping instances, there is a wrapper type
--   'PrettyCoq'. To pretty print a node @x@ of the Coq AST writer
--   @pretty (PrettyCoq x)@.
module Compiler.Coq.Pretty where

import           Language.Coq.Pretty            ( Gallina
                                                , renderGallina
                                                )

import           Compiler.Pretty

-- | Wrapper data type that makes a Coq AST node of type @a@ pretty printable.
newtype PrettyCoq a = PrettyCoq { unwrapPrettyCoq :: a }

-- | Pretty instance for nodes of the Coq AST.
--
--   When pretty printing a list of nodes, the individual documents are
--   concatenated with newlines.
instance Gallina a => Pretty (PrettyCoq a) where
  pretty = renderGallina . unwrapPrettyCoq
  prettyList = prettySeparated (line <> line)
