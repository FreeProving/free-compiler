-- | This module contains the parser for custom pragmas.
--
--   All custom pragmas have the format @{-# HASKELL_TO_COQ ... #-}@ (see
--   'customPragmaPattern').
--
--   The following custom pragmas are supported:
--
--     * @{-# HASKELL_TO_COQ <function> DECREASES ON <argument> #-}@
--       annotates the decreasing argument of a function declared in
--       the current module.

module Compiler.Haskell.PragmaParser
  ( parseCustomPragmas
  )
where

import           Control.Monad                  ( msum )
import           Data.Maybe                     ( catMaybes )
import           Text.RegexPR

import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Reporter

-- | Type alias for a function that creates a pragma AST node
--   from the capturing groups of a regular expression.
--
--   The given source span is the source span of the comment that
--   declares the pragma.
type CustomPragmaBuilder = SrcSpan -> [(Int, String)] -> Reporter HS.Pragma

-- | A regular expression for custom pragmas.
customPragmaPattern :: String
customPragmaPattern =
  "^#\\s*" ++ HS.customPragmaPrefix ++ "\\s+((\\S+(\\s*\\S)?)*)\\s*#$"

-- | Regular expressions and functions that create the pragma AST node
--   from the capturing groups of the match.
customPragmas :: [(String, CustomPragmaBuilder)]
customPragmas = [(decArgPattern, parseDecArgPragma)]

------------------------------------------------------------------------------
-- Decreasing arguments                                                     --
------------------------------------------------------------------------------

-- | A regular expression for a decreasing argument pragma.
decArgPattern :: String
decArgPattern = "^(\\S+)\\s+DECREASES\\s+ON\\s+(\\S+)$"

-- | Creates a decreasing argument pragma from the given capturing
--   groups for 'decArgPattern'.
parseDecArgPragma :: CustomPragmaBuilder
parseDecArgPragma srcSpan groups = do
  let Just funcIdent   = lookup 1 groups
      Just decArgIdent = lookup 2 groups
  return (HS.DecArgPragma srcSpan funcIdent decArgIdent)

------------------------------------------------------------------------------
-- Parser                                                                   --
------------------------------------------------------------------------------

-- | Parses custom pragmas (i.e., 'HS.DecArgPragma') from the comments of a
--   module.
parseCustomPragmas :: [HS.Comment] -> Reporter [HS.Pragma]
parseCustomPragmas = fmap catMaybes . mapM parseCustomPragma
 where
  -- | Parses a pragma from the given comment.
  --
  --   Returns @Nothing@ if the given comment is not a pragma or an
  --   unrecognised pragma.
  parseCustomPragma :: HS.Comment -> Reporter (Maybe HS.Pragma)
  parseCustomPragma (HS.LineComment _ _) = return Nothing
  parseCustomPragma (HS.BlockComment srcSpan text) =
    -- Test whether this comment is a custom pragma.
    case matchRegexPR customPragmaPattern text of
      Nothing          -> return Nothing
      Just (_, groups) -> do
        -- Try to match the contents of the pragma with the pattern
        -- of each custom pragma and return the result of the builder
        -- asociated with the first matching pattern.
        let Just text' = lookup 1 groups
        fmap msum
          $ flip mapM customPragmas
          $ \(pattern, action) -> case matchRegexPR pattern text' of
              Nothing -> do
                report $ Message srcSpan Warning $ "Unrecognised pragma"
                return Nothing
              Just (_, groups') -> do
                pragma <- action srcSpan groups'
                return (Just pragma)
