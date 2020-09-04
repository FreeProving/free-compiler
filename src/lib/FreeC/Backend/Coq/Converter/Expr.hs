-- | This module contains functions for converting Haskell expressions to Coq.
module FreeC.Backend.Coq.Converter.Expr where

import           Control.Monad                    ( (>=>) )

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
convertLiftedExpr :: LIR.Expr -> Converter Coq.Term
convertLiftedExpr (LIR.Con srcSpan name) = do
  qualid <- lookupIdentOrFail srcSpan IR.ValueScope name
  return $ Coq.Qualid qualid
convertLiftedExpr (LIR.SmartCon srcSpan name) = do
  qualid <- lookupSmartIdentOrFail srcSpan name
  return $ Coq.Qualid qualid
convertLiftedExpr (LIR.Var _ _ _ qualid) = return $ Coq.Qualid qualid
convertLiftedExpr (LIR.App _ func typeArgs effects args freeArgs) = do
  func' : args' <- mapM convertLiftedExpr $ func : args
  typeArgs' <- mapM convertLiftedType typeArgs
  let effectArgs' = map Coq.Qualid $ concatMap Coq.Base.selectArgs effects
  if freeArgs
    then return $ genericApply' func' effectArgs' typeArgs' args'
    else return $ Coq.app func' args'
convertLiftedExpr (LIR.If _ cond true false) = do
  cond' <- convertLiftedExpr cond
  true' <- convertLiftedExpr true
  false' <- convertLiftedExpr false
  return $ Coq.If Coq.SymmetricIf cond' Nothing true' false'
convertLiftedExpr (LIR.Case _ expr alts) = do
  expr' <- convertLiftedExpr expr
  alts' <- mapM convertLiftedAlt alts
  return $ Coq.match expr' alts'
convertLiftedExpr (LIR.Undefined _)
  = return $ Coq.Qualid Coq.Base.partialUndefined
convertLiftedExpr (LIR.ErrorExpr _) = return $ Coq.Qualid Coq.Base.partialError
convertLiftedExpr (LIR.IntLiteral _ value) = do
  let natValue = Coq.Num $ fromInteger (abs value)
      value'   | value < 0 = Coq.app (Coq.Qualid (Coq.bare "-")) [natValue]
               | otherwise = natValue
  return $ Coq.InScope value' Coq.Base.integerScope
convertLiftedExpr (LIR.StringLiteral _ str) = return
  $ Coq.InScope (Coq.string str) Coq.Base.stringScope
convertLiftedExpr (LIR.Lambda _ args rhs) = do
  let qualids  = map LIR.varPatCoqIdent args
      argTypes = map LIR.varPatType args
  argTypes' <- mapM (mapM convertLiftedType) argTypes
  rhs' <- convertLiftedExpr rhs
  return $ Coq.fun qualids argTypes' rhs'
convertLiftedExpr (LIR.Pure _ arg) = do
  arg' <- convertLiftedExpr arg
  generatePure arg'
convertLiftedExpr (LIR.Bind _ lhs rhs) = do
  lhs' <- convertLiftedExpr lhs
  rhs' <- convertLiftedExpr rhs
  return $ Coq.app (Coq.Qualid Coq.Base.freeBind) [lhs', rhs']
convertLiftedExpr (LIR.Share _) = return $ Coq.Qualid Coq.Base.share

-- | Converts a Haskell expression to Coq.
convertExpr :: IR.Expr -> Converter Coq.Term
convertExpr = liftExpr >=> convertLiftedExpr

-------------------------------------------------------------------------------
-- @case@ Expressions                                                        --
-------------------------------------------------------------------------------
-- Converts an alternative of a case expression in the lifted IR to Coq.
convertLiftedAlt :: LIR.Alt -> Converter Coq.Equation
convertLiftedAlt (LIR.Alt _ (LIR.ConPat srcSpan ident) varPats rhs) = do
  qualid <- lookupIdentOrFail srcSpan IR.ValueScope ident
  let varPats' = map (Coq.QualidPat . LIR.varPatCoqIdent) varPats
  rhs' <- convertLiftedExpr rhs
  return $ Coq.equation (Coq.ArgsPat qualid varPats') rhs'
