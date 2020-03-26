-- | This module contains a function for converting mutually recursive
--   Haskell functions to Coq.

module Compiler.Converter.FuncDecl.Rec
  ( convertRecFuncDecls
  )
where

import           Compiler.Analysis.RecursionAnalysis
import qualified Compiler.Coq.AST              as G
import qualified Compiler.IR.Syntax            as HS
import           Compiler.Monad.Converter

import           Compiler.Converter.FuncDecl.Rec.WithHelpers
import           Compiler.Converter.FuncDecl.Rec.WithSections

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
