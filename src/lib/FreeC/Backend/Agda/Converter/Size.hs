module FreeC.Backend.Agda.Converter.Size ( size, up ) where

import qualified FreeC.Backend.Agda.Base   as Agda.Base
import qualified FreeC.Backend.Agda.Syntax as Agda

-- | Hidden Size argument.
--
--   > Size
size :: Agda.Expr
size = Agda.Ident $ Agda.qname' Agda.Base.size

-- | Applies Agda function for larger size.
--
-- > e ↦ ↑ e
up :: Agda.Expr -> Agda.Expr
up = Agda.app $ Agda.Ident $ Agda.qname' Agda.Base.up

