-- | This module provides an interface to the pattern matching compiler and
--   case complition library by Malte Clement
--   <https://git.informatik.uni-kiel.de/stu204333/placc-thesis>.
--   We are using a slightly adapted version of the library located at
--   <https://github.com/FreeProving/haskell-src-transformations>.

module FreeC.Frontend.Haskell.PatternMatching
  ( transformPatternMatching
  )
where

import           Control.Monad                  ( void )
import           Control.Monad.State
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( mapMaybe )
import qualified Data.Set                      as Set

import           Application
import           FreshVars
import qualified Language.Haskell.Exts.Syntax  as H

import           FreeC.Environment
import           FreeC.Environment.ModuleInterface
import           FreeC.Environment.Entry
import           FreeC.Frontend.Haskell.Parser
import qualified FreeC.IR.Base.Prelude         as IR.Prelude
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pretty

-- | Constructs the initial state of the pattern matching compiler library.
--
--   The state is initialized with the (unqualified) entries from the prelude
--   module.
initialState :: Converter PMState
initialState = do
  Just preludeIface <- inEnv $ lookupAvailableModule IR.Prelude.modName
  let entries  = Set.toList (interfaceEntries preludeIface)
      entries' = mapMaybe makeConsMapEntry entries
      consMap  = Map.fromListWith (++) entries'
  return PMState { nextId      = 0
                 , constrMap   = Map.assocs consMap
                 , matchedPat  = []
                 , trivialCC   = False
                 , opt         = True
                 , debugOutput = ""
                 }

-- | Converts an entry of the 'Environment' to an entry of the constructor map
--   for the 'initialState'.
makeConsMapEntry :: EnvEntry -> Maybe (String, [(H.QName (), Int, Bool)])
makeConsMapEntry entry
  | not (isConEntry entry) = Nothing
  | otherwise = do
    returnType   <- entryReturnType entry
    typeConIdent <- extractTypeConIdent returnType
    conQName     <- mConQName
    return (typeConIdent, [(conQName, arity, isInfix)])
 where
  -- | Gets the name of the data type from the return type of the constructor.
  extractTypeConIdent :: IR.Type -> Maybe String
  extractTypeConIdent (IR.TypeCon _ (IR.UnQual name)) = extractIdent name
  extractTypeConIdent (IR.TypeCon _ (IR.Qual _ name)) = extractIdent name
  extractTypeConIdent (IR.TypeApp _ t1 _            ) = extractTypeConIdent t1
  extractTypeConIdent _                               = Nothing

  extractIdent :: IR.Name -> Maybe String
  extractIdent (IR.Ident  ident) = Just ident
  extractIdent (IR.Symbol sym  ) = Just sym

  -- | Generates the AST node for the name of the constructor by parsing the
  --   constructor name.
  mConQName :: Maybe (H.QName ())
  mConQName = void
    <$> evalReporter (parseQName (showPretty (unqualify (entryName entry))))

  -- | The number of arguments expected by the constructor.
  arity :: Int
  arity = entryArity entry

  -- | In Haskell infix operators start with a colon.
  isInfix :: Bool
  isInfix = case entryName entry of
    IR.Qual _ (IR.Symbol (':' : _)) -> True
    IR.UnQual (IR.Symbol (':' : _)) -> True
    _                               -> False

  -- | Converts a qualified identifier (e.g., the original entry name) to
  --   an unqualified identifier.
  unqualify :: IR.QName -> IR.QName
  unqualify (IR.Qual _ name) = IR.UnQual name
  unqualify (IR.UnQual name) = IR.UnQual name

-- | Applies the pattern matching transformation, guard elimination and case
--   completion.
--
--   Since the pattern matching compiler library does not support source
--   spans, location information is removed during the transformation.
transformPatternMatching :: H.Module SrcSpan -> Converter (H.Module SrcSpan)
transformPatternMatching haskellAst =
  transformPatternMatching' haskellAst <$> initialState

-- | Removes the source spans of the given Haskell AST and applies the pattern
--   matching compilation.
transformPatternMatching' :: H.Module SrcSpan -> PMState -> H.Module SrcSpan
transformPatternMatching' haskellAst = evalState $ do
  let haskellAst' = void haskellAst
  haskellAst'' <- processModule haskellAst'
  return (fmap (const NoSrcSpan) haskellAst'')
