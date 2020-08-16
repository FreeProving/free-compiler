-- | This module contains a function for processing the decreasing argument
--   pragma.
module FreeC.IR.Pragma where

import           Data.List             ( find, findIndex )

import           FreeC.Environment
import qualified FreeC.IR.Syntax       as IR
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pretty

-- | Inserts the decreasing argument's index annotated by the given pragma
--   into the environment.
--
--   Decreasing arguments can be annotated for all function declarations
--   in the current module (first argument).
--
--   All other pragmas are ignored.
addDecArgPragma :: [ IR.FuncDecl ] -> IR.Pragma -> Converter ()
addDecArgPragma funcDecls (IR.DecArgPragma srcSpan funcName decArg)
  = case find ((== funcName) . IR.funcDeclQName) funcDecls of
    Just IR.FuncDecl { IR.funcDeclArgs = args } -> case decArg of
      Left decArgIdent     ->
        case findIndex ((== decArgIdent) . IR.varPatIdent) args of
          Just decArgIndex ->
            modifyEnv $ defineDecArg funcName decArgIndex decArgIdent
          Nothing          -> reportFatal $ Message srcSpan Error
            $ "The function '" ++ showPretty funcName
            ++ "' does not have an argument pattern '" ++ decArgIdent ++ "'."
      Right decArgPosition
        | decArgPosition > 0 && decArgPosition <= length args -> do
          let decArgIndex = decArgPosition - 1
              decArgIdent = IR.varPatIdent (args !! decArgIndex)
          modifyEnv $ defineDecArg funcName decArgIndex decArgIdent
        | otherwise -> reportFatal $ Message srcSpan Error $ "The function '"
          ++ showPretty funcName ++ "' does not have an argument at index "
          ++ show decArgPosition ++ "."
    Nothing -> reportFatal $ Message srcSpan Error
      $ "The module does not declare a function '" ++ showPretty funcName
      ++ "'."
