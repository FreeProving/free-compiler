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
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( mapMaybe )
import qualified Data.Set                      as Set

import           Application
import           FreshVars
import qualified Language.Haskell.Exts.Syntax  as HSE

import           FreeC.Environment
import           FreeC.Environment.ModuleInterface
import           FreeC.Environment.Entry
import qualified FreeC.IR.Base.Prelude         as IR.Prelude
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter

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
makeConsMapEntry :: EnvEntry -> Maybe (String, [(HSE.QName (), Int, Bool)])
makeConsMapEntry entry
  | not (isConEntry entry) = Nothing
  | otherwise = do
    typeConIdent <- extractTypeConIdent (entryReturnType entry)
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

  -- | The @haskell-src-exts@ name of the constructor.
  conQName :: HSE.QName ()
  conQName = convertQName (entryName entry)

  -- | The number of arguments expected by the constructor.
  arity :: Int
  arity = entryArity entry

  -- | In Haskell infix operators start with a colon.
  isInfix :: Bool
  isInfix = case entryName entry of
    IR.Qual _ (IR.Symbol (':' : _)) -> True
    IR.UnQual (IR.Symbol (':' : _)) -> True
    _                               -> False

  -- | Converts a qualifiable IR name to a Haskell name.
  convertQName :: IR.QName -> HSE.QName ()
  convertQName qName = case Map.lookup qName specialNames of
    Just specialName -> HSE.Special () specialName
    Nothing          -> case qName of
      (IR.UnQual name) -> convertName name
      (IR.Qual _ name) -> convertName name

  -- | Converts an unqualified IR name to a Haskell name.
  convertName :: IR.Name -> HSE.QName ()
  convertName (IR.Ident  ident) = HSE.UnQual () (HSE.Ident () ident)
  convertName (IR.Symbol sym  ) = HSE.UnQual () (HSE.Symbol () sym)

  -- | Maps special IR constructor names to the corresponding Haskell name.
  specialNames :: Map IR.QName (HSE.SpecialCon ())
  specialNames = Map.fromList
    [ (IR.Prelude.unitConName   , HSE.UnitCon ())
    , (IR.Prelude.nilConName    , HSE.ListCon ())
    , (IR.Prelude.consConName   , HSE.Cons ())
    , (IR.Prelude.tupleConName 2, HSE.TupleCon () HSE.Boxed 2)
    ]

-- | Applies the pattern matching transformation, guard elimination and case
--   completion.
--
--   Since the pattern matching compiler library does not support source
--   spans, location information is removed during the transformation.
transformPatternMatching :: HSE.Module SrcSpan -> Converter (HSE.Module SrcSpan)
transformPatternMatching haskellAst =
  transformPatternMatching' haskellAst <$> initialState

-- | Removes the source spans of the given Haskell AST and applies the pattern
--   matching compilation.
transformPatternMatching' :: HSE.Module SrcSpan -> PMState -> HSE.Module SrcSpan
transformPatternMatching' haskellAst = evalPM $ do
  let haskellAst' = void haskellAst
  haskellAst'' <- processModule haskellAst'
  return (fmap (const NoSrcSpan) haskellAst'')
