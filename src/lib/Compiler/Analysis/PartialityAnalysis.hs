-- | This module contains functions for testing  whether a function
--   declaration is partial (i.e., needs a instance of the @Partial@
--   type class when translated to Coq).

module Compiler.Analysis.PartialityAnalysis
  ( isPartialFuncDecl
  )
where

import           Control.Monad.Extra            ( anyM )

import           Compiler.Analysis.DependencyExtraction
import           Compiler.Environment
import qualified Compiler.IR.Syntax            as HS
import           Compiler.Monad.Converter

-- | Tests whether the given function uses a partial function on its
--   right-hand side.
isPartialFuncDecl :: HS.FuncDecl -> Converter Bool
isPartialFuncDecl decl = anyM isPartialFuncName (funcDeclDependencies decl)
 where
  -- | Tests whether the function with the given name is partial.
  isPartialFuncName :: HS.QName -> Converter Bool
  isPartialFuncName name | name == HS.undefinedFuncName = return True
                         | name == HS.errorFuncName     = return True
                         | otherwise                    = inEnv $ isPartial name
