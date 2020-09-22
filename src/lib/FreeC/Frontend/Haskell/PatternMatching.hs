{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | This module provides an interface to the pattern matching compiler and
--   case completion library by Malte Clement
--   <https://git.informatik.uni-kiel.de/stu204333/placc-thesis>.
--   We are using a slightly adapted version of the library located at
--   <https://github.com/FreeProving/haskell-src-transformations>.
module FreeC.Frontend.Haskell.PatternMatching ( transformPatternMatching ) where

import qualified Data.Map.Strict                   as Map
import           HST.Frontend.HSE.Config           ( HSE )
import qualified HST.Application                   as HST
import qualified HST.Effect.Env                    as HST
import qualified HST.Effect.Fresh                  as HST
import qualified HST.Effect.GetOpt                 as HST
import qualified HST.Effect.InputFile              as HST
import qualified HST.Effect.Report                 as HST
import qualified HST.Effect.WithFrontend           as HST
import qualified HST.Environment                   as HST
import qualified HST.Frontend.Parser               as HST
import qualified HST.Frontend.Syntax               as HST
import qualified HST.Options                       as HST
import qualified HST.Util.Messages                 as HST
import qualified HST.Util.Selectors                as HST
import qualified Language.Haskell.Exts.Syntax      as HSE
import           Polysemy
  ( Member, Members, Sem, interpret, runM )
import           Polysemy.Embed                    ( Embed, embed )

import           FreeC.IR.SrcSpan
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter

-- | Applies the pattern matching transformation, guard elimination and case
--   completion.
--
--   Since the pattern matching compiler library does not support source
--   spans, location information is removed during the transformation.
transformPatternMatching
  :: HSE.Module SrcSpan -> Converter (HSE.Module SrcSpan)
transformPatternMatching inputModule = do
  let inputFilename     = undefined
      inputFileContents = undefined
  runM
    $ HST.runInputFileNoIO (Map.singleton inputFilename inputFileContents)
    $ reportToReporter
    $ HST.cancelToReport cancelMessage
    $ HST.runWithOptions HST.defaultOptions
    $ HST.runWithFrontendInstances @HSE
    $ transformPatternMatching' inputModule
 where
  cancelMessage :: HST.Message
  cancelMessage
    = HST.message HST.Info HST.NoSrcSpan "Pattern matching compilation failed."

transformPatternMatching'
  :: ( MonadReporter m
     , MonadConverter m
     , Members '[Embed m, HST.GetOpt, HST.Report, HST.WithFrontend HSE] r
     )
  => HSE.Module SrcSpan
  -> Sem r (HSE.Module SrcSpan)
transformPatternMatching' inputModule = do
  inputModule' <- HST.transformModule (HST.ParsedModuleHSE (fmap undefined inputModule))
  env <- initEnv inputModule'
  HST.runWithEnv env . HST.runFresh (HST.findIdentifiers inputModule') $ do
    outputModule' <- HST.processModule inputModule'
    outputModule <- HST.unTransformModule outputModule'
    return (fmap undefined (HST.getParsedModuleHSE outputModule))

-------------------------------------------------------------------------------
-- Environment Initialization                                                --
-------------------------------------------------------------------------------
initEnv :: (MonadConverter m, Member (Embed m) r)
        => HST.Module HSE
        -> Sem r (HST.Environment HSE)
initEnv _ = return HST.Environment
  { HST.envCurrentModule   = undefined
  , HST.envImportedModules = undefined
  , HST.envOtherEntries    = undefined
  }

-------------------------------------------------------------------------------
-- Interpretation for `Report` Effect                                        --
-------------------------------------------------------------------------------
-- | Interprets a computation that can report messages in terms of a
--   'MonadReporter'.
reportToReporter :: (MonadReporter m, Members '[Embed m, HST.InputFile] r)
                 => Sem (HST.Report ': r) a
                 -> Sem r a
reportToReporter = interpret \case
  HST.Report msg      -> embed . report =<< convertMessage msg
  HST.ReportFatal msg -> embed . reportFatal =<< convertMessage msg

-- | Converts a message that has been reported by the pattern matching compiler
--   to a message that can be reported by a 'MonadReporter'.
convertMessage :: Member HST.InputFile r => HST.Message -> Sem r Message
convertMessage (HST.Message severity srcSpan text) = do
  srcSpan' <- convertMsgSrcSpan srcSpan
  let severity' = convertSeverity severity
  return (Message srcSpan' severity' text)

-- | Converts the source span of a message that has been reported by the
--   pattern matching compiler to our source span data type.
convertMsgSrcSpan
  :: Member HST.InputFile r => Maybe HST.MsgSrcSpan -> Sem r SrcSpan
convertMsgSrcSpan Nothing           = return NoSrcSpan
convertMsgSrcSpan (Just msgSrcSpan) = do
  contents <- HST.getInputFile (HST.msgSrcSpanFilePath msgSrcSpan)
  return SrcSpan
    { srcSpanFilename    = HST.msgSrcSpanFilePath msgSrcSpan
    , srcSpanStartLine   = HST.msgSrcSpanStartLine msgSrcSpan
    , srcSpanStartColumn = HST.msgSrcSpanStartColumn msgSrcSpan
    , srcSpanEndLine     = HST.msgSrcSpanEndLine msgSrcSpan
    , srcSpanEndColumn   = HST.msgSrcSpanEndColumn msgSrcSpan
    , srcSpanCodeLines   = take (HST.msgSrcSpanEndLine msgSrcSpan)
        (drop (HST.msgSrcSpanStartLine msgSrcSpan) (lines contents))
    }

-- | Converts the severity of a message that has been reported by the pattern
--   matching compiler to our message severity data type.
convertSeverity :: HST.Severity -> Severity
convertSeverity HST.Internal = Internal
convertSeverity HST.Error    = Error
convertSeverity HST.Warning  = Warning
convertSeverity HST.Info     = Info
convertSeverity HST.Debug    = Debug
