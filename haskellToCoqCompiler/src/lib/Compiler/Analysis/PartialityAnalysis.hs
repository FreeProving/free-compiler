module Compiler.Analysis.PartialityAnalysis where

import           Data.Graph
import           Data.List                      ( nub )
import           Data.Tuple.Extra

import           Compiler.Analysis.DependencyGraph

-- | Identifies function declatations that are either partial because they
--   contain error terms or depend on a function that are partial in turn.
partialFunctions :: DependencyGraph -> [DGKey]
partialFunctions (DependencyGraph graph getEntry _) = map (snd3 . getEntry)
                                                          indirect
 where
  -- | Vertices of functions that are partial because they contain error terms.
  direct :: [Vertex]
  direct = filter (containsErrorTerm . getEntry) (vertices graph)

  -- | Vertices of functions that are partial because they contain error
  --   terms or depend on other partial functions.
  indirect :: [Vertex]
  indirect = nub (concatMap (reachable (transposeG graph)) direct)

  -- | Tests whether a function contains error terms.
  containsErrorTerm :: DGEntry -> Bool
  containsErrorTerm (_, _, deps) = any (`elem` deps) [errorKey, undefinedKey]
