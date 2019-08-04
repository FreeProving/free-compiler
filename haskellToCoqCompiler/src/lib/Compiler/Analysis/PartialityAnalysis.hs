-- | This module contains a function that uses the function dependency graph
--   to identify partial function declarations.

module Compiler.Analysis.PartialityAnalysis where

import           Data.Graph
import           Data.List                      ( nub )
import           Data.Tuple.Extra

import           Compiler.Analysis.DependencyGraph

-- | Identifies function declatations that are either partial because they
--   contain error terms or depend on a function that are partial in turn.
--
--   The first argument contains the names of (predefined) functions that are
--   known to be partial.
identifyPartialFuncs :: [DGKey] -> DependencyGraph -> [DGKey]
identifyPartialFuncs predefined (DependencyGraph graph getEntry _) = map
  (snd3 . getEntry)
  indirect
 where
  -- | Vertices of functions that are partial because they contain error terms.
  direct :: [Vertex]
  direct = filter (isDirectlyPartial . getEntry) (vertices graph)

  -- | Vertices of functions that are partial because they contain error
  --   terms or depend on other partial functions.
  indirect :: [Vertex]
  indirect = nub (concatMap (reachable (transposeG graph)) direct)

  -- | Tests whether a function contains error terms or references to
  --   predefined partial functions.
  isDirectlyPartial :: DGEntry -> Bool
  isDirectlyPartial (_, _, deps) =
    any (`elem` deps) ([errorKey, undefinedKey] ++ predefined)
