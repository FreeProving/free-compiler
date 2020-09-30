{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}

{-# OPTIONS_GHC -Wno-orphans #-}

-- | This module provides an interface to the pattern matching compiler and
--   case completion library by Malte Clement
--   <https://git.informatik.uni-kiel.de/stu204333/placc-thesis>.
--   We are using a slightly adapted version of the library located at
--   <https://github.com/FreeProving/haskell-src-transformations>.
module FreeC.Frontend.Haskell.PatternMatching ( transformPatternMatching ) where

import           Control.Monad                     ( zipWithM )
import           Data.Map.Strict                   ( Map )
import qualified Data.Map.Strict                   as Map
import           Data.Maybe                        ( mapMaybe )
import qualified Data.Set                          as Set
import           Data.Tuple.Extra                  ( (&&&), (***) )
import qualified HST.Application                   as HST
import qualified HST.Effect.Env                    as HST
import qualified HST.Effect.Fresh                  as HST
import qualified HST.Effect.GetOpt                 as HST
import qualified HST.Effect.InputFile              as HST
import qualified HST.Effect.InputModule            as HST
import qualified HST.Effect.Report                 as HST
import qualified HST.Environment                   as HST
import           HST.Frontend.HSE.Config           ( HSE )
import qualified HST.Frontend.HSE.From             as FromHSE
import qualified HST.Frontend.HSE.To               as ToHSE
import qualified HST.Frontend.Syntax               as HST
import qualified HST.Options                       as HST
import qualified HST.Util.Messages                 as HST
import qualified HST.Util.PrettyName               as HST
import qualified HST.Util.Selectors                as HST
import qualified Language.Haskell.Exts             as HSE
import           Polysemy
  ( Member, Members, Sem, interpret, runM )
import           Polysemy.Embed                    ( Embed, embed )

import           FreeC.Environment.Entry
import           FreeC.Environment.LookupOrFail
import           FreeC.Environment.ModuleInterface
import qualified FreeC.IR.Base.Prelude             as IR.Prelude
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax                   as IR
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter

-- | Applies the pattern matching transformation, guard elimination and case
--   completion.
transformPatternMatching
  :: HSE.Module SrcSpan -> Converter (HSE.Module SrcSpan)
transformPatternMatching inputModule = do
  let inputSrcSpan      = HSE.ann inputModule
      inputFilename
        = [srcSpanFilename inputSrcSpan | hasSrcSpanFilename inputSrcSpan]
      inputFileContents = [unlines (srcSpanCodeLines inputSrcSpan)
                          | hasSourceCode inputSrcSpan
                          ]
      inputFileMap      = Map.fromList (zip inputFilename inputFileContents)
  runM
    $ HST.runInputFileNoIO inputFileMap
    $ reportToReporter
    $ HST.cancelToReport cancelMessage
    $ HST.runWithOptions HST.defaultOptions
    $ transformPatternMatching' inputModule
 where
  cancelMessage :: HST.Message
  cancelMessage
    = HST.message HST.Info HST.NoSrcSpan "Pattern matching compilation failed."

-- | Like 'transformPatternMatching' but uses the @haskell-src-transformations@
--   effect stack instead of the 'Converter' monad.
transformPatternMatching'
  :: Members '[Embed Converter, HST.GetOpt, HST.Report] r
  => HSE.Module SrcSpan
  -> Sem r (HSE.Module SrcSpan)
transformPatternMatching' inputModule = do
  inputModule' <- FromHSE.transformModule inputModule
  env <- initEnv inputModule'
  HST.runWithEnv env . HST.runFresh (HST.findIdentifiers inputModule') $ do
    outputModule <- HST.processModule inputModule'
    return (ToHSE.transformModule outputModule)

-------------------------------------------------------------------------------
-- Source Spans                                                              --
-------------------------------------------------------------------------------
-- | Front end configuration type for the @haskell-src-exts@ front end with
--   source spans of type 'SrcSpan'.
type Frontend = HSE SrcSpan

-- | Converts a source span to an HST source span.
instance FromHSE.TransformSrcSpan SrcSpan where
  transformSrcSpan srcSpan = HST.SrcSpan srcSpan HST.MsgSrcSpan
    { HST.msgSrcSpanFilePath    = srcSpanFilename srcSpan
    , HST.msgSrcSpanStartLine   = srcSpanStartLine srcSpan
    , HST.msgSrcSpanStartColumn = srcSpanStartColumn srcSpan
    , HST.msgSrcSpanEndLine     = srcSpanEndLine srcSpan
    , HST.msgSrcSpanEndColumn   = srcSpanEndColumn srcSpan
    }

-- | Extracts the actual source span from an HST source span.
instance ToHSE.TransformSrcSpan SrcSpan where
  transformSrcSpan (HST.SrcSpan originalSrcSpan _) = originalSrcSpan
  transformSrcSpan HST.NoSrcSpan                   = NoSrcSpan

-------------------------------------------------------------------------------
-- Environment Initialization                                                --
-------------------------------------------------------------------------------
-- | Initializes the environment of the pattern matching compiler for the
--   given module.
initEnv :: Member (Embed Converter) r
        => HST.Module Frontend
        -> Sem r (HST.Environment Frontend)
initEnv inputModule@(HST.Module _ _ _ imports _) = do
  let importSrcSpans = map (ToHSE.transformSrcSpan . HST.importSrcSpan) imports
      importNames    = map (HST.prettyName . HST.importModule) imports
  ifaces
    <- embed $ zipWithM lookupAvailableModuleOrFail importSrcSpans importNames
  preludeIface
    <- embed $ lookupAvailableModuleOrFail NoSrcSpan IR.Prelude.modName
  return HST.Environment
    { HST.envCurrentModule   = HST.createModuleInterface inputModule
    , HST.envImportedModules = zipWith
        (\imp iface -> ([imp], convertModuleInterface iface)) imports ifaces
    , HST.envOtherEntries    = convertModuleInterface preludeIface
    }

-- | Converts the given module interface to a module interface of the pattern
--   matching compiler.
convertModuleInterface :: ModuleInterface -> HST.ModuleInterface Frontend
convertModuleInterface iface = HST.ModuleInterface
  { HST.interfaceModName     = Just
      (HST.ModuleName HST.NoSrcSpan (interfaceModName iface))
  , HST.interfaceDataEntries = Map.fromList
      (map (convertQName *** convertDataEntry) (Map.assocs dataEntries))
  , HST.interfaceConEntries  = Map.fromList
      (map (convertQName *** convertConEntry) (Map.assocs conEntries))
  }
 where
  -- | All entries that are exported by the module.
  exportedEntries :: [EnvEntry]
  exportedEntries = filter
    ((`Set.member` interfaceExports iface) . entryScopedName)
    (Set.toList (interfaceEntries iface))

  -- | All entries of data constructors exported by the module.
  --
  --   The keys of the map are the original names of the entries.
  conEntries :: Map IR.QName EnvEntry
  conEntries = Map.fromList
    (map (entryName &&& id) (filter isConEntry exportedEntries))

  -- | All entries of data types exported by the module.
  --
  --   The keys of the map are the original names of the entries.
  dataEntries :: Map IR.QName EnvEntry
  dataEntries = Map.fromList
    (map (entryName &&& id) (filter isDataEntry exportedEntries))

  -- | Converts a potentially qualified IR name to an unqualified or special
  --   HST name.
  convertQName :: IR.QName -> HST.QName Frontend
  convertQName qName = case Map.lookup qName specialNames of
    Just specialName -> HST.Special HST.NoSrcSpan specialName
    Nothing          -> case qName of
      (IR.UnQual name) -> convertName name
      (IR.Qual _ name) -> convertName name

  -- | Converts an unqualified IR name to an HST name.
  convertName :: IR.Name -> HST.QName Frontend
  convertName (IR.Ident ident) = HST.UnQual HST.NoSrcSpan
    (HST.Ident HST.NoSrcSpan ident)
  convertName (IR.Symbol sym)  = HST.UnQual HST.NoSrcSpan
    (HST.Symbol HST.NoSrcSpan sym)

  -- | Maps special IR constructor names to the corresponding HST name.
  specialNames :: Map IR.QName (HST.SpecialCon Frontend)
  specialNames = Map.fromList
    [ (IR.Prelude.unitConName, HST.UnitCon HST.NoSrcSpan)
    , (IR.Prelude.nilConName, HST.NilCon HST.NoSrcSpan)
    , (IR.Prelude.consConName, HST.ConsCon HST.NoSrcSpan)
    , (IR.Prelude.tupleConName 2, HST.TupleCon HST.NoSrcSpan HST.Boxed 2)
    ]

  -- | Tests whether the given name belongs to an infix constructor (i.e.,
  --   is a symbol that starts with a colon).
  isInfixConQName :: IR.QName -> Bool
  isInfixConQName (IR.Qual _ (IR.Symbol (':' : _))) = True
  isInfixConQName (IR.UnQual (IR.Symbol (':' : _))) = True
  isInfixConQName _ = False

  -- | Converts the entry of an exported data type to an HST data type entry.
  convertDataEntry :: EnvEntry -> HST.DataEntry Frontend
  convertDataEntry entry = HST.DataEntry
    { HST.dataEntryName = convertQName (entryName entry)
    , HST.dataEntryCons = map convertConEntry
        (mapMaybe (flip Map.lookup conEntries) (entryConsNames entry))
    }

  -- | Converts the entry of an exported data constructor to an HST constructor
  --   entry.
  convertConEntry :: EnvEntry -> HST.ConEntry Frontend
  convertConEntry entry = HST.ConEntry
    { HST.conEntryName    = convertQName (entryName entry)
    , HST.conEntryArity   = entryArity entry
    , HST.conEntryIsInfix = isInfixConQName (entryName entry)
    , HST.conEntryType    = extractConEntryType entry
    }

  -- | Extracts the type name of an exported data constructor entry and
  --   transforms it to an HST name.
  extractConEntryType :: EnvEntry -> HST.TypeName Frontend
  extractConEntryType = convertQName . extractTypeConQName . entryReturnType

  -- | Gets the name of the data type from the return type of the constructor.
  extractTypeConQName :: IR.Type -> IR.QName
  extractTypeConQName (IR.TypeCon _ conName) = conName
  extractTypeConQName (IR.TypeApp _ t1 _) = extractTypeConQName t1
  extractTypeConQName _
    = error "extractTypeConQName: Expected type constructor."

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
    , srcSpanCodeLines   = take (HST.msgSrcSpanEndLine msgSrcSpan - 1)
        (drop (HST.msgSrcSpanStartLine msgSrcSpan - 1) (lines contents))
    }

-- | Converts the severity of a message that has been reported by the pattern
--   matching compiler to our message severity data type.
convertSeverity :: HST.Severity -> Severity
convertSeverity HST.Internal = Internal
convertSeverity HST.Error    = Error
convertSeverity HST.Warning  = Warning
convertSeverity HST.Info     = Info
convertSeverity HST.Debug    = Debug
