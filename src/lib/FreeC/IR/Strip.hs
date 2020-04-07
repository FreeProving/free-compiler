-- | This module contains functions for removing information from the AST
--   of the intermediate language.
--
--   These functions are useful to simplify tests or make the output of
--   pretty instances actually pretty by removing irrelevant information.

module FreeC.IR.Strip
  ( -- * Removing expression type annotations
    StripExprType(..)
  )
where

import           Data.Maybe                     ( fromJust )

import qualified FreeC.IR.Syntax               as IR
import           FreeC.IR.Subterm

-------------------------------------------------------------------------------
-- Removing expression type annotations                                      --
-------------------------------------------------------------------------------

-- | Type class for AST nodes from which expression type annotations can
--   be removed.
class StripExprType node where
  stripExprType :: node -> node

-- | Strips the expression type annotations from function declarations.
instance StripExprType IR.FuncDecl where
  stripExprType funcDecl =
    funcDecl { IR.funcDeclRhs = stripExprType (IR.funcDeclRhs funcDecl) }

-- | Strips the type annotation of the given expression and of its
--   sub-expressions recursively.
instance StripExprType IR.Expr where
  stripExprType expr = fromJust
    (replaceChildTerms expr { IR.exprTypeSchema = Nothing }
                       (map stripExprType (childTerms expr))
    )
