{-# LANGUAGE FlexibleInstances, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module contains a 'Pretty' instance for nodes of the Coq AST.
--
--   We need the language extensions @FlexibleInstances@ and
--   @UndecidableInstances@ because we want to declare the 'Pretty' instance
--   for all pretty printable components of the Coq AST (instances of
--   'Gallina') and not just specific types of nodes.
--
--   Because the 'Pretty' and 'Gallina' type class are both declared in
--   external modules, we have to disable orphan instance error messages
--   with the compiler flag @-Wno-orphans@ for this module.
module Compiler.Pretty.Coq where

import           Language.Coq.Pretty            ( Gallina, renderGallina )

import           Compiler.Pretty

-- | Pretty instance for nodes of the Coq AST.
--
--   When pretty printing a list of nodes, the individual documents are
--   concatenated with newlines.
instance {-# OVERLAPPABLE #-} Gallina a => Pretty a where
  pretty = renderGallina
  prettyList = prettySeparated line
