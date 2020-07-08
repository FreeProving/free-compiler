-- | Implements the lifted IR to Agda translation for expressions.

module FreeC.Backend.Agda.Converter.Expr
  ( convertLiftedExpr
  )
where

import qualified FreeC.Backend.Agda.Syntax     as Agda
import           FreeC.Backend.Agda.Converter.Free
                                                ( generatePure
                                                , bind
                                                , undefinedExpr
                                                , errorExpr
                                                )

import           FreeC.Environment.LookupOrFail ( lookupAgdaSmartIdentOrFail
                                                , lookupAgdaValIdentOrFail
                                                )
import qualified FreeC.LiftedIR.Syntax         as LIR
import           FreeC.Monad.Converter

-- | Converts an expression from lifted IR to an Agda expression.
convertLiftedExpr :: LIR.Expr -> Converter Agda.Expr
convertLiftedExpr (LIR.Con srcSpan name) =
  Agda.Ident <$> lookupAgdaValIdentOrFail srcSpan name
convertLiftedExpr (LIR.SmartCon srcSpan name) =
  Agda.Ident <$> lookupAgdaSmartIdentOrFail srcSpan name
convertLiftedExpr (LIR.Var _ _ name) = return $ Agda.Ident name
convertLiftedExpr (LIR.App _ expr _ _ args) =
  Agda.appN <$> convertLiftedExpr expr <*> mapM convertLiftedExpr args
convertLiftedExpr (LIR.If _ cond true false) =
  Agda.ite
    <$> convertLiftedExpr cond
    <*> convertLiftedExpr true
    <*> convertLiftedExpr false
convertLiftedExpr (LIR.Case _ discr alts) =
  Agda.caseOf <$> convertLiftedExpr discr <*> mapM convertLiftedAlt alts
convertLiftedExpr (LIR.IntLiteral _ val ) = return $ Agda.intLiteral val
convertLiftedExpr (LIR.Lambda _ args rhs) = do
  let args' = map (Agda.unqualify . LIR.varPatAgdaIdent) args
  Agda.lambda args' <$> convertLiftedExpr rhs
convertLiftedExpr (LIR.Pure _ expr) = generatePure <$> convertLiftedExpr expr
convertLiftedExpr (LIR.Bind _ arg k) =
  bind <$> convertLiftedExpr arg <*> convertLiftedExpr k
convertLiftedExpr (LIR.Undefined _    ) = return $ undefinedExpr
convertLiftedExpr (LIR.ErrorExpr _ msg) = return $ errorExpr msg

-- | Converts a single pattern from a LIR case expression to an Agda
--   expression.
convertLiftedAlt :: LIR.Alt -> Converter Agda.LamClause
convertLiftedAlt (LIR.Alt _ (LIR.ConPat srcSpan name) vars rhs) = do
  conPat' <- Agda.IdentP <$> lookupAgdaValIdentOrFail srcSpan name
  let varPats = map (Agda.IdentP . LIR.varPatAgdaIdent) vars
  Agda.lamClause (foldl Agda.appP conPat' varPats) <$> convertLiftedExpr rhs
