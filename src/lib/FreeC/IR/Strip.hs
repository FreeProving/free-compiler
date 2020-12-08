-- | This module contains functions for removing information from the AST
--   of the intermediate language.
--
--   These functions are useful to simplify tests or make the output of
--   pretty instances actually pretty by removing irrelevant information.
module FreeC.IR.Strip
  ( -- * Removing Expression Type Annotations
    StripExprType(..)
  ) where

import           Data.Maybe       ( fromJust )

import           FreeC.IR.Subterm
import qualified FreeC.IR.Syntax  as IR

-------------------------------------------------------------------------------
-- Removing Expression Type Annotations                                      --
-------------------------------------------------------------------------------
-- | Type class for AST nodes from which expression type annotations can
--   be removed.
class StripExprType node where
  stripExprType :: node -> node

-- | When expression type annotations can be removed from a node, they can also
--   be removed from a list of those nodes.
instance StripExprType node => StripExprType [node] where
  stripExprType = map stripExprType

-- | Strips the expression type annotations from all declarations in a module.
instance StripExprType contents => StripExprType (IR.ModuleOf contents) where
  stripExprType ast
    = ast { IR.modContents = stripExprType (IR.modContents ast) }

-- | Strips the expression type annotations from top-level function
--   declarations.
instance StripExprType IR.TopLevelDecl where
  stripExprType decl | IR.isTopLevelFuncDecl decl = IR.TopLevelFuncDecl
                       (stripExprType (IR.topLevelFuncDecl decl))
                     | otherwise = decl

-- | Strips the expression type annotations from function declarations.
instance StripExprType IR.FuncDecl where
  stripExprType funcDecl
    = funcDecl { IR.funcDeclRhs = stripExprType (IR.funcDeclRhs funcDecl) }

-- | Strips the type annotation of the given expression and of its
--   sub-expressions recursively.
instance StripExprType IR.Expr where
  stripExprType expr = fromJust
    (replaceChildTerms expr { IR.exprTypeScheme = Nothing }
     (map stripExprType (childTerms expr)))
