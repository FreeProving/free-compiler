-- | This module contains a function for converting mutually recursive
--   Haskell functions to Coq.

module Compiler.Backend.Coq.Converter.FuncDecl.Rec
  ( convertRecFuncDecls
  )
where

import qualified Compiler.Backend.Coq.Syntax   as G
import           Compiler.Backend.Coq.Converter.FuncDecl.Rec.WithHelpers
import           Compiler.Backend.Coq.Converter.FuncDecl.Rec.WithSections
import           Compiler.Analysis.RecursionAnalysis
import qualified Compiler.IR.Syntax            as HS
import           Compiler.Monad.Converter

-- | Converts (mutually) recursive Haskell function declarations to Coq.
--
--   The function declarations are analysed first. If they contain constant
--   arguments (i.e. arguments that are passed unchanged between recursive
--   calls), they are converted using a @Section@ sentence (see
--   'convertRecFuncDeclsWithHelpers'). Otherwise they are converted into
--   helper and main functions (see 'convertRecFuncDeclsWithSection').
convertRecFuncDecls :: [HS.FuncDecl] -> Converter [G.Sentence]
convertRecFuncDecls decls = localEnv $ do
  -- If there are constant arguments, move them to a section.
  constArgs <- identifyConstArgs decls
  if null constArgs
    then convertRecFuncDeclsWithHelpers decls
    else convertRecFuncDeclsWithSection constArgs decls
