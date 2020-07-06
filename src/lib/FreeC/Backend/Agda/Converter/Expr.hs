module FreeC.Backend.Agda.Converter.Expr
  ( convertLiftedExpr
  )
where

import           Control.Applicative            ( (<|>) )
import           Data.Maybe                     ( fromMaybe )

import qualified FreeC.Backend.Agda.Syntax     as Agda
import           FreeC.Backend.Agda.Converter.Free
                                                ( generatePure
                                                , bind
                                                )

import           FreeC.Environment              ( lookupEntry )
import           FreeC.Environment.Entry        ( entryAgdaIdent )
import           FreeC.Environment.LookupOrFail ( lookupAgdaSmartIdentOrFail
                                                , lookupAgdaValIdentOrFail
                                                )
import           FreeC.Environment.Renamer      ( renameAndDefineAgdaVar )
import qualified FreeC.IR.Syntax               as IR
import qualified FreeC.LiftedIR.Syntax         as LIR
import           FreeC.Monad.Converter

-- | Converts an expression from lifted IR to an Agda expression.
convertLiftedExpr :: LIR.Expr -> Converter Agda.Expr
convertLiftedExpr (LIR.Con _ _ _) = fail "Missing case for constructors!"
convertLiftedExpr (LIR.SmartCon srcSpan name _) =
  Agda.Ident <$> lookupAgdaSmartIdentOrFail srcSpan name
convertLiftedExpr (LIR.Var _ name _) =
  Agda.Ident <$> lookupAgdaFreshOrValIdent name
convertLiftedExpr (LIR.App _ expr _ _ args _) =
  foldl Agda.app <$> convertLiftedExpr expr <*> mapM convertLiftedExpr args
convertLiftedExpr (LIR.If _ cond true false _) =
  Agda.ite
    <$> convertLiftedExpr cond
    <*> convertLiftedExpr true
    <*> convertLiftedExpr false
convertLiftedExpr (LIR.Case _ discr alts) =
  Agda.caseOf <$> convertLiftedExpr discr <*> mapM convertLiftedAlt alts
convertLiftedExpr (LIR.IntLiteral _ val _ ) = return $ Agda.intLiteral val
convertLiftedExpr (LIR.Lambda _ args rhs _) = localEnv $ do
  args' <- mapM (fmap Agda.unqualify . convertLiftedVarPat) args
  Agda.lambda args' <$> convertLiftedExpr rhs
convertLiftedExpr (LIR.Pure _ expr _) = generatePure <$> convertLiftedExpr expr
convertLiftedExpr (LIR.Bind _ arg k _) =
  bind <$> convertLiftedExpr arg <*> convertLiftedExpr k
convertLiftedExpr (LIR.Undefined _ _  ) = undefined
convertLiftedExpr (LIR.ErrorExpr _ _ _) = undefined

-- | Converts a single pattern from a LIR case expression to an Agda
--   expression.
--
--   The pattern of an alternative binds new variables used by the right-hand
--   side. This function therefore uses @localEnv@.
convertLiftedAlt :: LIR.Alt -> Converter Agda.LamClause
convertLiftedAlt (LIR.Alt _ (LIR.ConPat srcSpan name) vars rhs) = localEnv $ do
  conPat' <- Agda.IdentP <$> lookupAgdaValIdentOrFail srcSpan name
  varPats <- mapM (fmap Agda.IdentP . convertLiftedVarPat) vars
  Agda.lamClause (foldl Agda.appP conPat' varPats) <$> convertLiftedExpr rhs

-- | We translate a var pattern by defining a new variable with  preferably the
--   same name.
--
--   Var patterns are used on the left-hand side of lambdas and case expressions.
convertLiftedVarPat :: LIR.VarPat -> Converter Agda.QName
convertLiftedVarPat (LIR.VarPat srcSpan name _) = renameAndDefineAgdaVar
  srcSpan
  False
  (fromMaybe (fail "") $ IR.identFromQName $ name)
  Nothing

-- | Looks up an identifier, which is either in the value or fresh scope.
--
--   Adding an alternative instance for @ReporterT@ and @ConverterT@ would allow
--   us to use @lookupOrFail@ functions.
lookupAgdaFreshOrValIdent :: LIR.QName -> Converter (Agda.QName)
lookupAgdaFreshOrValIdent name = do
  valueName <- inEnv $ lookupEntry IR.ValueScope name
  freshName <- inEnv $ lookupEntry IR.FreshScope name
  maybe (fail $ "lookup for " ++ show name ++ " failed!")
        (pure . entryAgdaIdent)
        (valueName <|> freshName)
