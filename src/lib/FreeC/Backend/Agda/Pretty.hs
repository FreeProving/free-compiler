{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains 'Pretty' instances for the Agda AST.
--
--   The Agda library has its own 'Agda.Pretty' class in "Agda.Utils.Pretty". Therefore
--   we cannot instance every @a@ with an @Agda.Pretty@ instance with our
--   'Pretty' instance without generating overlapping instances for basic types
--   (e.g. 'String').
--   We introduce the wrapper datatype 'PrettyAgda' to avoid the overlapping
--   instances and explicitly declare 'Pretty' instances for for common AST
--   nodes.
module FreeC.Backend.Agda.Pretty
  ( prettyAgda
  )
where

-- import qualified Agda.Syntax.Concrete.Generic  as Agda

-- We need just he pretty instances from 'Agda.Syntax.Concrete.Pretty'.
import qualified Agda.Syntax.Concrete.Pretty    ( )
import qualified Agda.Utils.Pretty             as Agda

import qualified FreeC.Backend.Agda.Syntax     as Agda
import           FreeC.Pretty

-- | Wrapper data type that makes any 'Agda.Pretty' instance pretty printable.
newtype PrettyAgda a = PrettyAgda { unPrettyAgda :: a }

-- | Pretty instance for all Agda internal pretty printable types.
instance (Agda.Pretty a) => Pretty (PrettyAgda a) where
  pretty = prettyString . Agda.prettyShow . unPrettyAgda

-- | Helper function for printing 'Agda.Pretty' printable types @a@ to a 'Doc'
--   used by our pretty printer.
prettyAgda :: (Agda.Pretty a) => a -> Doc
prettyAgda = pretty . PrettyAgda

-- | 'Agda.Expr's are a common AST node.
instance Pretty Agda.Expr where
  pretty = prettyAgda

-- | 'Agda.Declaration's  are a common AST node.
instance Pretty Agda.Declaration where
  pretty = prettyAgda
