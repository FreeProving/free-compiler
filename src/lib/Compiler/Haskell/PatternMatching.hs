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

import           Application
import           FreshVars
import qualified Language.Haskell.Exts.Syntax  as H

import           Compiler.Haskell.SrcSpan

-- | Initial state of the pattern matching compiler library.
initialState :: PMState
initialState = PMState
  { nextId      = 0
  , constrMap   = specialCons
  , funcId      = ["undefined"]
  , matchedPat  = []
  , trivialCC   = False
  , opt         = True
  , debugOutput = ""
  }

-- | Applies the pattern matching transformation, guard elimination and case
--   completion.
--
--   Since the pattern matching compiler library does not support source
--   spans, location information is removed during the transformation.
transformPatternMatching :: H.Module SrcSpan -> H.Module SrcSpan
transformPatternMatching haskellAst = flip evalState initialState $ do
  let haskellAst' = (fmap (const ()) haskellAst)
  haskellAst'' <- processModule haskellAst'
  return (fmap (const NoSrcSpan) haskellAst'')
