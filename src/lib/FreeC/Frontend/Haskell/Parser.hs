-- | This module contains functions for parsing Haskell modules and other
--   nodes of the Haskell AST.
--
--   We are using the @haskell-src-ext@ package for parsing. This module just
--   provides an interface for the actual parser and configures the parser
--   appropriately.

module FreeC.Frontend.Haskell.Parser
  ( parseHaskell
    -- * Modules
  , parseModule
  , parseModuleWithComments
  , parseModuleFile
  , parseModuleFileWithComments
    -- * Declarations
  , parseDecl
    -- * Types
  , parseType
  , parseTypeSchema
    -- * Expressions
  , parseExpr
    -- * Identifiers
  , parseQName
  )
where

import           Control.Monad.IO.Class         ( MonadIO(..) )
import           Data.Composition               ( (.:)
                                                , (.:.)
                                                )

import qualified Language.Haskell.Exts.Comments
                                               as H
import           Language.Haskell.Exts.Extension
                                                ( Language(..)
                                                , Extension(..)
                                                , KnownExtension(..)
                                                )
import           Language.Haskell.Exts.Fixity   ( Fixity
                                                , infix_
                                                , infixl_
                                                , infixr_
                                                )
import           Language.Haskell.Exts.Parser   ( ParseMode(..)
                                                , ParseResult(..)
                                                , Parseable(..)
                                                )
import           Language.Haskell.Exts.SrcLoc   ( SrcSpanInfo )
import qualified Language.Haskell.Exts.Syntax  as H

import           FreeC.Frontend.Haskell.SrcSpanConverter
import           FreeC.IR.SrcSpan
import           FreeC.IR.Syntax               as IR
import           FreeC.Monad.Reporter

-- | Custom parameters for parsing a Haskell source file with the given name.
--
--   Only the given language extensions are enabled and no additional
--   language extensions can be enabled using pragmas.
makeParseMode :: [KnownExtension] -> String -> ParseMode
makeParseMode enabledExts filename = ParseMode
  { parseFilename         = filename
  , baseLanguage          = Haskell2010
  , extensions            = map EnableExtension enabledExts
  , ignoreLanguagePragmas = True
  , ignoreLinePragmas     = True
    -- If this is set to @Nothing@, user defined fixities are ignored while
    -- parsing.
  , fixities              = Just predefinedFixities
  , ignoreFunctionArity   = True
  }

-- | Fixities for all predefined operators and infix constructors.
predefinedFixities :: [Fixity]
predefinedFixities = concat
  [ -- Prelude.
    infixr_ 8 ["^"]
  , infixl_ 7 ["*"]
  , infixl_ 6 ["+", "-"]
  , infixr_ 5 [":"]
  , infix_ 4 ["==", "/=", "<", "<=", ">=", ">"]
  , infixr_ 3 ["&&"]
  , infixr_ 2 ["||"]
  -- QuickCheck.
  , infixr_ 0 ["==>"]
  , infixr_ 1 [".&&.", ".||."]
  , infix_ 4 ["===", "=/="]
  ]

-- | Parses a node of the Haskell AST.
parseHaskell
  :: (Functor ast, Parseable (ast SrcSpanInfo), MonadReporter r)
  => String -- ^ The name of the Haskell source file.
  -> String -- ^ The Haskell source code.
  -> r (ast SrcSpan)
parseHaskell = fmap fst .: parseHaskellWithComments

-- | Like 'parseHaskell' but allows language extensions to be enabled.
parseHaskellWithExts
  :: (Functor ast, Parseable (ast SrcSpanInfo), MonadReporter r)
  => [KnownExtension] -- ^ The extensions to enable.
  -> String           -- ^ The name of the Haskell source file.
  -> String           -- ^ The Haskell source code.
  -> r (ast SrcSpan)
parseHaskellWithExts = fmap fst .:. parseHaskellWithCommentsAndExts

-- | Like 'parseHaskell' but returns comments in addition to the AST.
parseHaskellWithComments
  :: (Functor ast, Parseable (ast SrcSpanInfo), MonadReporter r)
  => String -- ^ The name of the Haskell source file.
  -> String -- ^ The Haskell source code.
  -> r (ast SrcSpan, [IR.Comment])
parseHaskellWithComments = parseHaskellWithCommentsAndExts []

-- | Like 'parseHaskellWithComments' but allows language extensions to be
--   enabled.
parseHaskellWithCommentsAndExts
  :: (Functor ast, Parseable (ast SrcSpanInfo), MonadReporter r)
  => [KnownExtension] -- ^ The extensions to enable.
  -> String           -- ^ The name of the Haskell source file.
  -> String           -- ^ The Haskell source code.
  -> r (ast SrcSpan, [IR.Comment])
parseHaskellWithCommentsAndExts enabledExts filename contents =
  case parseWithComments parseMode contents of
    ParseOk (node, comments) -> return
      ( fmap (toMessageSrcSpan :: SrcSpanInfo -> SrcSpan) node
      , map convertComment comments
      )
    ParseFailed loc msg ->
      reportFatal $ Message (toMessageSrcSpan loc) Error msg
 where
  -- | Configuration of the Haskell parser.
  parseMode :: ParseMode
  parseMode = makeParseMode enabledExts filename

  -- | A map that maps the name of the Haskell source file to the lines of
  --   source code.
  srcFiles :: SrcFileMap
  srcFiles = mkSrcFileMap [mkSrcFile filename contents]

  -- | Converts the source spans generated by the @haskell-src-exts@ package
  --   to source spans that can be used for pretty printing reported messages.
  --
  --   The 'srcFiles' is needed because when pretty printing a message,
  --   an excerpt of the code that caused the message to be reported is shown.
  toMessageSrcSpan :: ConvertableSrcSpan l => l -> SrcSpan
  toMessageSrcSpan = convertSrcSpanWithCode srcFiles

  -- | Unlike all other AST nodes of @haskell-src-exts@, the
  --   'Language.Haskell.Exts.Comments.Comment' data type does
  --   not have a type parameter for the source span information.
  --   Therefore, we have to convert comments in this phase already.
  convertComment :: H.Comment -> IR.Comment
  convertComment (H.Comment isBlockComment srcSpan text)
    | isBlockComment = IR.BlockComment (toMessageSrcSpan srcSpan) text
    | otherwise      = IR.LineComment (toMessageSrcSpan srcSpan) text

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------

-- | Parses a Haskell module.
--
--   Syntax errors cause a fatal error message to be reported.
parseModule
  :: MonadReporter r
  => String  -- ^ The name of the Haskell source file.
  -> String  -- ^ The Haskell source code.
  -> r (H.Module SrcSpan)
parseModule = parseHaskell

-- | Like 'parseModule' but returns the comments in addtion to the AST.
parseModuleWithComments
  :: MonadReporter r
  => String  -- ^ The name of the Haskell source file.
  -> String  -- ^ The Haskell source code.
  -> r (H.Module SrcSpan, [IR.Comment])
parseModuleWithComments = parseHaskellWithComments

-- | Loads and parses a Haskell module from the file with the given name.
parseModuleFile
  :: (MonadIO r, MonadReporter r)
  => String -- ^ The name of the Haskell source file.
  -> r (H.Module SrcSpan)
parseModuleFile = fmap fst . parseModuleFileWithComments

-- | Like 'parseModuleFile' but returns the comments in addtion to the AST.
parseModuleFileWithComments
  :: (MonadIO r, MonadReporter r)
  => String -- ^ The name of the Haskell source file.
  -> r (H.Module SrcSpan, [IR.Comment])
parseModuleFileWithComments filename = do
  contents <- liftIO $ readFile filename
  parseModuleWithComments filename contents

-------------------------------------------------------------------------------
-- Declarations                                                              --
-------------------------------------------------------------------------------

-- | Parses a Haskell type.
parseDecl
  :: MonadReporter r
  => String -- ^ The name of the Haskell source file.
  -> String -- ^ The Haskell source code.
  -> r (H.Decl SrcSpan)
parseDecl = parseHaskell

-------------------------------------------------------------------------------
-- Types                                                                   --
-------------------------------------------------------------------------------

-- | Parses a Haskell type.
parseType
  :: MonadReporter r
  => String -- ^ The name of the Haskell source file.
  -> String -- ^ The Haskell source code.
  -> r (H.Type SrcSpan)
parseType = parseHaskell

-- | Parses a Haskell type schema.
--
--   A type schema is a type with an optional explicit @forall@ quantifier.
--   This requires the @ExplicitForAll@ language extension to be enabled.
parseTypeSchema
  :: MonadReporter r
  => String -- ^ The name of the Haskell source file.
  -> String -- ^ The Haskell source code.
  -> r (H.Type SrcSpan)
parseTypeSchema = parseHaskellWithExts [ExplicitForAll]

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Parses a Haskell expression.
parseExpr
  :: MonadReporter r
  => String -- ^ The name of the Haskell source file.
  -> String -- ^ The Haskell source code.
  -> r (H.Exp SrcSpan)
parseExpr = parseHaskell

-------------------------------------------------------------------------------
-- Identifiers                                                               --
-------------------------------------------------------------------------------

-- | Parses an optionally qualified Haskell identifier or symbol of a
--   constructor.
--
--   Since there is no 'Parseable' instance for 'H.QName', the given string
--   is parsed as a pattern instead. The name of the constructor is extracted
--   from the pattern.
--
--   TODO now that we have an IR parser, we probably don't need this anymore.
parseQName :: MonadReporter r => String -> r (H.QName SrcSpan)
parseQName input = parseHaskell "<parseQName>" input >>= qNameFromPat
 where
  qNameFromPat :: MonadReporter r => H.Pat SrcSpan -> r (H.QName SrcSpan)
  qNameFromPat (H.PApp _ qname []) = return qname
  qNameFromPat (H.PList srcSpan []) =
    return (H.Special srcSpan (H.ListCon srcSpan))
  qNameFromPat (H.PParen _ pat) = qNameFromPat pat
  qNameFromPat _ =
    reportFatal
      $  Message NoSrcSpan Error
      $  "Expected symbol or identifier, got "
      ++ input
