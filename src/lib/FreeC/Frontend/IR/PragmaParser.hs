-- | This module contains the parser for custom pragmas.
--
--   All custom pragmas have the format @{-\# FreeC ... \#-}@ (see
--   'customPragmaPattern').
--
--   The following custom pragmas are supported:
--
--     * @{-\# FreeC <function> DECREASES ON <argument> \#-}@
--       annotates the decreasing argument of a function declared in
--       the current module.
module FreeC.Frontend.IR.PragmaParser ( parseCustomPragmas ) where

import           Control.Applicative  ( (<|>) )
import           Control.Monad        ( forM, msum )
import           Control.Monad.Extra  ( mapMaybeM )
import           Text.RegexPR

import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax      as IR
import           FreeC.Monad.Reporter

-- | Type alias for a function that creates a pragma AST node
--   from the capturing groups of a regular expression.
--
--   The given source span is the source span of the comment that
--   declares the pragma.
type CustomPragmaBuilder = SrcSpan -> [ (Int, String) ] -> Reporter IR.Pragma

-- | A regular expression for custom pragmas.
customPragmaPattern :: String
customPragmaPattern
  = "^#\\s*" ++ IR.customPragmaPrefix ++ "\\s+((\\S+(\\s*\\S)?)*)\\s*#$"

-- | Regular expressions and functions that create the pragma AST node
--   from the capturing groups of the match.
customPragmas :: [ (String, CustomPragmaBuilder) ]
customPragmas = [(decArgPattern, parseDecArgPragma)]

-------------------------------------------------------------------------------
-- Decreasing Arguments                                                      --
-------------------------------------------------------------------------------
-- | A regular expression for a decreasing argument pragma.
decArgPattern :: String
decArgPattern = "^(\\S+)\\s+DECREASES\\s+ON\\s+((\\S+)|ARGUMENT\\s+(\\d+))$"

-- | Creates a decreasing argument pragma from the given capturing
--   groups for 'decArgPattern'.
parseDecArgPragma :: CustomPragmaBuilder
parseDecArgPragma srcSpan groups = do
  let Just funcName = IR.UnQual . IR.Ident <$> lookup 1 groups
      Just decArg   = (Left <$> lookup 3 groups)
        <|> (Right . read <$> lookup 4 groups)
  return (IR.DecArgPragma srcSpan funcName decArg)

-------------------------------------------------------------------------------
-- Parser                                                                    --
-------------------------------------------------------------------------------
-- | Parses custom pragmas (i.e., 'IR.DecArgPragma') from the comments of a
--   module.
parseCustomPragmas :: [ IR.Comment ] -> Reporter [ IR.Pragma ]
parseCustomPragmas = mapMaybeM parseCustomPragma

-- | Parses a pragma from the given comment.
--
--   Returns @Nothing@ if the given comment is not a pragma or an
--   unrecognized pragma.
parseCustomPragma :: IR.Comment -> Reporter (Maybe IR.Pragma)
parseCustomPragma (IR.LineComment _ _)           = return Nothing
parseCustomPragma (IR.BlockComment srcSpan text) =
  -- Test whether this comment is a custom pragma.
  case matchRegexPR customPragmaPattern text of
    Nothing          -> return Nothing
    Just (_, groups) -> do
      let Just text' = lookup 1 groups
      -- Try to match the contents of the pragma with the pattern
      -- of each custom pragma and return the result of the builder
      -- associated with the first matching pattern.
      fmap msum
        $ forM customPragmas
        $ \(regex, action) -> case matchRegexPR regex text' of
          Nothing           -> do
            report $ Message srcSpan Warning $ "Unrecognized pragma"
            return Nothing
          Just (_, groups') -> do
            pragma <- action srcSpan groups'
            return (Just pragma)
