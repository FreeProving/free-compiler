-- | This module contains functions for converting Haskell expressions to Coq.
module FreeC.Backend.Coq.Converter.Expr where

import           Control.Monad                    ( (>=>), zipWithM )
import           Data.Maybe                       ( maybeToList )

import qualified FreeC.Backend.Coq.Base           as Coq.Base
import           FreeC.Backend.Coq.Converter.Free
import           FreeC.Backend.Coq.Converter.Type
import qualified FreeC.Backend.Coq.Syntax         as Coq
import           FreeC.Environment.LookupOrFail
import qualified FreeC.IR.Syntax                  as IR
import           FreeC.LiftedIR.Converter.Expr
import qualified FreeC.LiftedIR.Syntax            as LIR
import           FreeC.Monad.Converter

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------
-- | Converts a lifted IR expression to a Coq term.
convertLiftedExpr :: Bool -> LIR.Expr -> Converter Coq.Term
convertLiftedExpr _ (LIR.Con srcSpan name) = do
  qualid <- lookupIdentOrFail srcSpan IR.ValueScope name
  return $ Coq.Qualid qualid
convertLiftedExpr _ (LIR.SmartCon srcSpan name) = do
  qualid <- lookupSmartIdentOrFail srcSpan name
  return $ Coq.Qualid qualid
convertLiftedExpr _ (LIR.Var _ _ _ qualid) = return $ Coq.Qualid qualid
convertLiftedExpr translateEvalArgs (LIR.App _ func typeArgs effects args freeArgs) = do
  func' : args' <- mapM (convertLiftedExpr translateEvalArgs) $ func : args
  typeArgs' <- mapM convertLiftedType typeArgs
  let explicitEffectArgs' = concatMap Coq.Base.selectExplicitArgs effects
      implicitEffectArgs' = concatMap Coq.Base.selectImplicitArgs effects
      implicitTypeArgs'   = concatMap
        (flip Coq.Base.selectTypedImplicitArgs $ length typeArgs) effects
  if freeArgs
    then return
      $ genericApply' func' explicitEffectArgs' implicitEffectArgs' typeArgs'
      implicitTypeArgs' args'
    else return $ Coq.app func' args'
convertLiftedExpr translateEvalArgs (LIR.If _ cond true false) = do
  cond' <- convertLiftedExpr translateEvalArgs cond
  true' <- convertLiftedExpr translateEvalArgs true
  false' <- convertLiftedExpr translateEvalArgs false
  return $ Coq.If Coq.SymmetricIf cond' Nothing true' false'
convertLiftedExpr translateEvalArgs (LIR.Case _ expr alts) = do
  expr' <- convertLiftedExpr translateEvalArgs expr
  alts' <- zipWithM convertLiftedAlt (repeat translateEvalArgs) alts
  return $ Coq.match expr' alts'
convertLiftedExpr _ (LIR.Undefined _)
  = return $ Coq.Qualid Coq.Base.partialUndefined
convertLiftedExpr _ (LIR.ErrorExpr _) = return $ Coq.Qualid Coq.Base.partialError
convertLiftedExpr _ (LIR.Trace _) = return $ Coq.Qualid Coq.Base.trace
convertLiftedExpr _ (LIR.IntLiteral _ value) = do
  let natValue = Coq.Num $ fromInteger (abs value)
      value'   | value < 0 = Coq.app (Coq.Qualid (Coq.bare "-")) [natValue]
               | otherwise = natValue
  return $ Coq.InScope value' Coq.Base.integerScope
convertLiftedExpr _ (LIR.StringLiteral _ str) = return
  $ Coq.InScope (Coq.string str) Coq.Base.stringScope
convertLiftedExpr translateEvalArgs (LIR.Lambda _ args rhs) = do
  let qualids  = map LIR.varPatCoqIdent args
      argTypes = map LIR.varPatType args
  argTypes' <- mapM (mapM convertLiftedType) argTypes
  rhs' <- convertLiftedExpr translateEvalArgs rhs
  return $ Coq.fun qualids argTypes' rhs'
convertLiftedExpr translateEvalArgs (LIR.Pure _ arg) = do
  arg' <- convertLiftedExpr translateEvalArgs arg
  generatePure arg'
convertLiftedExpr translateEvalArgs (LIR.Bind _ lhs rhs) = do
  lhs' <- convertLiftedExpr translateEvalArgs lhs
  rhs' <- convertLiftedExpr translateEvalArgs rhs
  return $ Coq.app (Coq.Qualid Coq.Base.freeBind) [lhs', rhs']
convertLiftedExpr translateEvalArgs (LIR.Share _ arg argType) =
    case translateEvalArgs of
         True -> do
            arg' <- convertLiftedExpr translateEvalArgs arg
            argType' <- mapM convertLiftedType argType
            return
                $ genericApply' (Coq.Qualid Coq.Base.share)
                [genericApply Coq.Base.strategyArg [Coq.Underscore] [] []] []
                (maybeToList argType') [Coq.Base.implicitArg] [arg']
         False ->  do
             arg' <- convertLiftedExpr translateEvalArgs arg
             generatePure arg'
convertLiftedExpr translateEvalArgs (LIR.Call _ arg argType)
    = case translateEvalArgs of
           True -> do
                arg' <- convertLiftedExpr translateEvalArgs arg
                argType' <- mapM convertLiftedType argType
                return
                    $ genericApply' (Coq.Qualid Coq.Base.call)
                    [genericApply Coq.Base.strategyArg [Coq.Underscore] [] []] [] (maybeToList argType') [] [arg']
           False -> do
               arg' <- convertLiftedExpr translateEvalArgs arg
               generatePure arg'

convertExpr' :: Bool -> IR.Expr -> Converter Coq.Term
convertExpr' translateEvalArgs = liftExpr >=> (convertLiftedExpr translateEvalArgs)
-- | Converts a Haskell expression to Coq.
convertExpr :: IR.Expr -> Converter Coq.Term
convertExpr = convertExpr' True

-------------------------------------------------------------------------------
-- @case@ Expressions                                                        --
-------------------------------------------------------------------------------
-- Converts an alternative of a case expression in the lifted IR to Coq.
convertLiftedAlt :: Bool -> LIR.Alt -> Converter Coq.Equation
convertLiftedAlt translateEvalArgs (LIR.Alt _ (LIR.ConPat srcSpan ident) varPats rhs) = do
  qualid <- lookupIdentOrFail srcSpan IR.ValueScope ident
  let varPats' = map (Coq.QualidPat . LIR.varPatCoqIdent) varPats
  rhs' <- convertLiftedExpr translateEvalArgs rhs
  return $ Coq.equation (Coq.ArgsPat qualid varPats') rhs'
