-- | This module provides an interface to the pattern matching compiler and
--   case complition library by Malte Clement
--   <https://git.informatik.uni-kiel.de/stu204333/placc-thesis>.
--   We are using a slightly adapted version of the library located at
--   <https://git.informatik.uni-kiel.de/stu203400/haskell-code-transformation>.

module Compiler.Haskell.PatternMatching
  ( transformPatternMatching
  )
where

import           Control.Monad.State
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( catMaybes )

import           Application
import           FreshVars
import qualified Language.Haskell.Exts.Syntax  as H

import           Compiler.Environment
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.Parser
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty

-- | Constructs the initial state of the pattern matching compiler library.
initialState :: Converter PMState
initialState = do
  cons <- inEnv definedCons
  let entries = catMaybes (map makeConsMapEntry cons)
      consMap = Map.fromListWith (++) entries
  return PMState
    { nextId      = 0
    , constrMap   = Map.assocs consMap
    , funcId      = ["undefined"]
    , matchedPat  = []
    , trivialCC   = False
    , opt         = True
    , debugOutput = ""
    }

-- | Converts an entry of the 'Environment' to an entry of the constructor map
--   for the 'initialState'.
makeConsMapEntry
  :: (HS.Name, [Maybe HS.Type], Maybe HS.Type)
  -> Maybe (String, [(H.QName (), Int, Bool)])
makeConsMapEntry (conName, mArgs, mReturnType) = do
  returnType   <- mReturnType
  typeConIdent <- extractTypeConIdent returnType
  conQName     <- mConQName
  case conQName of
    H.Qual _ _ _ -> Nothing -- Ignore qualified names (e.g. @Prelude.True@)
    _            -> return (typeConIdent, [(conQName, arity, isInfix)])
 where
  -- | Gets the name of the data type from the return type of the constructor.
  extractTypeConIdent :: HS.Type -> Maybe String
  extractTypeConIdent (HS.TypeCon _ (HS.Ident ident)) = Just ident
  extractTypeConIdent (HS.TypeCon _ (HS.Symbol sym)) = Just sym
  extractTypeConIdent (HS.TypeApp _ t1 _) = extractTypeConIdent t1
  extractTypeConIdent _ = Nothing

  -- | Generates the AST node for the name of the constructor by parsing the
  --   constructor name.
  mConQName :: Maybe (H.QName ())
  mConQName =
    fmap (fmap (const ())) $ evalReporter $ parseQName $ showPretty conName

  -- | The number of arguments expected by the constructor.
  arity :: Int
  arity = length mArgs

  -- | In Haskell infix operators start with a colon.
  isInfix :: Bool
  isInfix = case conName of
    HS.Symbol (':' : _) -> True
    _                   -> False

-- | Applies the pattern matching transformation, guard elimination and case
--   completion.
--
--   Since the pattern matching compiler library does not support source
--   spans, location information is removed during the transformation.
transformPatternMatching :: H.Module SrcSpan -> Converter (H.Module SrcSpan)
transformPatternMatching haskellAst =
  initialState >>= return . transformPatternMatching' haskellAst

transformPatternMatching' :: H.Module SrcSpan -> PMState -> H.Module SrcSpan
transformPatternMatching' haskellAst = evalState $ do
  let haskellAst' = (fmap (const ()) haskellAst)
  haskellAst'' <- processModule haskellAst'
  return (fmap (const NoSrcSpan) haskellAst'')
