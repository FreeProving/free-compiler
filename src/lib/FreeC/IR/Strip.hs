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

import qualified FreeC.IR.Syntax               as HS
import           FreeC.IR.Subterm

-------------------------------------------------------------------------------
-- Removing expression type annotations                                      --
-------------------------------------------------------------------------------

-- | Type class for AST nodes from which expression type annotations can
--   be removed.
class StripExprType node where
  stripExprType :: node -> node

-- | Strips the expression type annotations from function declarations.
instance StripExprType HS.FuncDecl where
  stripExprType funcDecl =
    funcDecl { HS.funcDeclRhs = stripExprType (HS.funcDeclRhs funcDecl) }

-- | Strips the type annotation of the given expression and of its
--   sub-expressions recursively.
instance StripExprType HS.Expr where
  stripExprType expr = fromJust
    (replaceChildTerms expr { HS.exprTypeSchema = Nothing }
                       (map stripExprType (childTerms expr))
    )
