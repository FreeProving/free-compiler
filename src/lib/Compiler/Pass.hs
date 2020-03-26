-- | This module contains the data type that is used to model individual
--   passes of the compiler's pipeline (see also "Compiler.Pipeline").

module Compiler.Pass where

import           Control.Monad                  ( (>=>) )

import           Compiler.Monad.Converter

-- | Compiler passes are transformations of AST nodes of type @a@.
--
--   The 'Converter' monad is used to preserve state across passes and
--   to report messages.
type Pass a = a -> Converter a

-- | Runs the given compiler pass.
runPass :: Pass a -> a -> Converter a
runPass = id

-- | Runs the given compiler passes after each other.
--
--   The given initial value is passed to the first pass. The result is
--   passed to the subsequent pass. The result of the final pass is returned.
runPasses :: [Pass a] -> a -> Converter a
runPasses = foldr (>=>) return

-- | Creates a pass that runs the given sub-pipeline on each component of its
--   input returned by the first given function and recombines the results
--   of the sub-pipelines into the result of the entire pass using the second
--   given function.
subPipelinePass :: (a -> [b]) -> (a -> [b] -> a) -> [Pass b] -> Pass a
subPipelinePass getComponents updateComponents childPasses input = do
  let components = getComponents input
  components' <- mapM (runPasses childPasses) components
  return (updateComponents input components')
