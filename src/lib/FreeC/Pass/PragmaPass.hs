-- | This module contains a compiler pass that processes pragmas.
--
--   = Specification
--
--   == Preconditions
--
--   There are no special requirements.
--
--   == Translation
--
--    * If there is a pragma of the form @{-# FreeC f DECREASES ON xᵢ #-}@
--      or @{-# FreeC f DECREASES ON ARGUMENT i #-}@ and a declaration
--      @f x₁ … xᵢ … xₙ = e@, the index @i - 1@ and identifier @xᵢ@ are
--      inserted into the environment as the decreasing argument of @f@.
--
--   == Postconditions
--
--    * There is an entry for all explicitly annotated decreasing arguments
--      in the environment.
--
--   == Error Cases
--
--    * If there is a pragmaof the form @{-# FreeC f DECREASES ON xᵢ #-}@ or
--      @{-# FreeC f DECREASES ON ARGUMENT i #-}@, but there is no such
--      function declaration or the function does not have an argument with
--      the specified name or at the specified position, a fatal error is
--      reported.


module FreeC.Pass.PragmaPass ( pragmaPass ) where

import           Data.List             ( find, findIndex )

import           FreeC.Environment
import qualified FreeC.IR.Syntax       as IR
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pass
import           FreeC.Pretty

-- | A pass that processes the pragmas of a module.
pragmaPass :: Pass IR.Module IR.Module
pragmaPass ast = do
  mapM_ (addDecArgPragma (IR.modFuncDecls ast)) (IR.modPragmas ast)
  return ast

-- | Inserts the decreasing argument's index annotated by the given pragma
--   into the environment.
--
--   Decreasing arguments can be annotated for all function declarations
--   in the current module (first argument).
--
--   All other pragmas are ignored.
addDecArgPragma :: [IR.FuncDecl] -> IR.Pragma -> Converter ()
addDecArgPragma funcDecls (IR.DecArgPragma srcSpan funcName decArg)
  = case find ((== funcName) . IR.funcDeclQName) funcDecls of
    Just IR.FuncDecl { IR.funcDeclArgs = args } -> case decArg of
      Left decArgIdent     ->
        case findIndex ((== decArgIdent) . IR.varPatIdent) args of
          Just decArgIndex ->
            modifyEnv $ defineDecArg funcName decArgIndex decArgIdent
          Nothing          -> reportFatal
            $ Message srcSpan Error
            $ "The function '"
            ++ showPretty funcName
            ++ "' does not have an argument pattern '"
            ++ decArgIdent
            ++ "'."
      Right decArgPosition
        | decArgPosition > 0 && decArgPosition <= length args -> do
          let decArgIndex = decArgPosition - 1
              decArgIdent = IR.varPatIdent (args !! decArgIndex)
          modifyEnv $ defineDecArg funcName decArgIndex decArgIdent
        | otherwise -> reportFatal
          $ Message srcSpan Error
          $ "The function '"
          ++ showPretty funcName
          ++ "' does not have an argument at index "
          ++ show decArgPosition
          ++ "."
    Nothing -> reportFatal
      $ Message srcSpan Error
      $ "The module does not declare a function '"
      ++ showPretty funcName
      ++ "'."
