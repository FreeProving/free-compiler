-- | This module contains a function for converting mutually recursive
--   Haskell functions to Coq.

module FreeC.Backend.Coq.Converter.FuncDecl.Rec
  ( convertRecFuncDecls
  )
where

import           FreeC.Backend.Coq.Analysis.ConstantArguments
import qualified FreeC.Backend.Coq.Syntax      as G
import           FreeC.Backend.Coq.Converter.FuncDecl.Rec.WithHelpers
import           FreeC.Backend.Coq.Converter.FuncDecl.Rec.WithSections
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter

-- | Converts (mutually) recursive Haskell function declarations to Coq.
--
--   The function declarations are analysed first. If they contain constant
--   arguments (i.e. arguments that are passed unchanged between recursive
--   calls), they are converted using a @Section@ sentence (see
--   'convertRecFuncDeclsWithHelpers'). Otherwise they are converted into
--   helper and main functions (see 'convertRecFuncDeclsWithSection').
convertRecFuncDecls :: [IR.FuncDecl] -> Converter [G.Sentence]
convertRecFuncDecls decls = localEnv $ do
  -- If there are constant arguments, move them to a section.
  constArgs <- identifyConstArgs decls
  if null constArgs
    then convertRecFuncDeclsWithHelpers decls
    else convertRecFuncDeclsWithSection constArgs decls
