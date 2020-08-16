{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains a 'Pretty' instance for nodes of the Coq AST.
--
--   Since we want to have a pretty instance for all 'Gallina' instances
--   but want to avoid overlapping instances, there is a wrapper type
--   'PrettyCoq'. To pretty print a node @x@ of the Coq AST you can write
--   @pretty (PrettyCoq x)@.
--
--   There are instances for the actual node of commonly pretty printed types
--   of nodes.
module FreeC.Backend.Coq.Pretty ( PrettyCoq(..), prettyCoq ) where

import qualified Language.Coq.Gallina as Coq
import           Language.Coq.Pretty ( Gallina, renderGallina )

import           FreeC.Pretty

-- | Wrapper data type that makes a Coq AST node of type @a@ pretty printable.
newtype PrettyCoq a = PrettyCoq { unPrettyCoq :: a }

-- | Pretty instance for nodes of the Coq AST.
--
--   When pretty printing a list of nodes, the individual documents are
--   concatenated with newlines.
instance Gallina a => Pretty (PrettyCoq a) where
  pretty     = renderGallina . unPrettyCoq

  prettyList = prettySeparated (line <> line)

-- | Pretty prints the given Coq AST node.
prettyCoq :: Gallina a => a -> Doc
prettyCoq = pretty . PrettyCoq

-- | Terms often need to be pretty printed in the tests.
instance Pretty Coq.Term where
  pretty     = prettyCoq

  prettyList = prettyList . map PrettyCoq

-- | Sentences often need to be pretty printed in the tests and when writing
--   the generated Coq code to the console or a file.
instance Pretty Coq.Sentence where
  pretty     = prettyCoq

  prettyList = prettyList . map PrettyCoq
