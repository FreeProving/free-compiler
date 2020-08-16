-- | This module contains the data type that is used to model individual
--   passes of the compiler's pipeline (see also "FreeC.Pipeline").
module FreeC.Pass where

import           Control.Monad ( (>=>) )

import           FreeC.Monad.Converter

-- | Compiler passes are transformations of AST nodes of type @a@.
--
--   The 'Converter' monad is used to preserve state across passes and
--   to report messages.
type Pass a = a -> Converter a

-- | Runs the given compiler pass.
runPass :: Pass a -> a -> Converter a
runPass = id

-- | Runs the given compiler passes consecutively.
--
--   The given initial value is passed to the first pass. The result is
--   passed to the subsequent pass. The result of the final pass is returned.
runPasses :: [Pass a] -> a -> Converter a
runPasses = foldr (>=>) return

-- | Creates a pass that runs the given sub-pipeline on each component of its
--   input (which are extracted using first given function) and recombines the
--   results of the sub-pipelines into the result of the entire pass (using the
--   second given function).
subPipelinePass
  :: (a -> [b])
  -- ^ The helper function extracting the components of the input.
  -> (a -> [b] -> a)
  -- ^ The helper function recombining the results of the sub passes.
  -> [Pass b]
  -- ^ The sub passes running on each component of the input.
  -> Pass a
subPipelinePass getComponents updateComponents childPasses input = do
  let components = getComponents input
  components' <- mapM (runPasses childPasses) components
  return (updateComponents input components')
