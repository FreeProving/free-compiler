-- | This module contains utility functions for the @Map@ data type.
--
--   This module is intended to be imported qualified, to avoid name clashes
--   with Prelude functions, e.g.
--   @
--   import qualified Data.Map as Map
--   @

module Compiler.Util.Map where

import           Data.Map                       ( Map )
import qualified Data.Map.Strict               as Map

-- | Version of @mapM@ for maps.
mapM :: (Ord k, Monad m) => (a -> m b) -> Map k a -> m (Map k b)
mapM f m = do
  let (ks, vs) = unzip (Map.assocs m)
  vs' <- Prelude.mapM f vs
  return (Map.fromList (zip ks vs'))
