module Compiler.Application.Debug where

import           Control.Monad.IO.Class
import           System.IO                      ( hPutStrLn
                                                , stderr
                                                )

-- | Prints the given debugging message to @stderr@
putDebug :: MonadIO m => String -> m ()
putDebug = liftIO . hPutStrLn stderr
