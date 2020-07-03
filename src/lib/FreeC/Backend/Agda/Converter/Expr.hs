module FreeC.Backend.Agda.Converter.Expr
  ( convertLiftedExpr
  )
where

import           Control.Applicative            ( (<|>) )
import           Data.Maybe                     ( fromJust )

import qualified FreeC.Backend.Agda.Syntax     as Agda
import           FreeC.Backend.Agda.Converter.Free
                                                ( generatePure
                                                , bind
                                                )

import           FreeC.Environment              ( lookupEntry )
import           FreeC.Environment.Entry        ( entryAgdaIdent )
import           FreeC.Environment.LookupOrFail ( lookupAgdaSmartIdentOrFail )
import qualified FreeC.IR.Syntax               as IR
import qualified FreeC.LiftedIR.Syntax         as LIR
import           FreeC.Monad.Converter

convertLiftedExpr :: LIR.Expr -> Converter Agda.Expr
convertLiftedExpr (LIR.Con _ _ _) = fail "Missing case for constructors!"
convertLiftedExpr (LIR.SmartCon srcSpan name _) =
  Agda.Ident <$> lookupAgdaSmartIdentOrFail srcSpan name
convertLiftedExpr (LIR.Var _ name _) = do
  valueName <- inEnv $ lookupEntry IR.ValueScope name
  freshName <- inEnv $ lookupEntry IR.FreshScope name
  -- Adding an alternative instance for @ReporterT@ and @ConverterT@ would allow us to use @lookupOrFail@ functions.
  return $ Agda.Ident $ entryAgdaIdent $ fromJust $ valueName <|> freshName
convertLiftedExpr (LIR.App _ expr _ _ args _) =
  foldl Agda.app <$> convertLiftedExpr expr <*> mapM convertLiftedExpr args
convertLiftedExpr (LIR.If _ cond true false _) =
  Agda.ite
    <$> convertLiftedExpr cond
    <*> convertLiftedExpr true
    <*> convertLiftedExpr false
convertLiftedExpr (LIR.Case _ _ _ _       ) = undefined
convertLiftedExpr (LIR.Undefined _ _      ) = undefined
convertLiftedExpr (LIR.ErrorExpr  _ _   _ ) = undefined
convertLiftedExpr (LIR.IntLiteral _ val _ ) = return $ Agda.intLiteral val
convertLiftedExpr (LIR.Lambda _ args rhs _) = do
  Agda.lambda <$> mapM lookupVarPat args <*> convertLiftedExpr rhs
convertLiftedExpr (LIR.Pure _ expr _) = generatePure <$> convertLiftedExpr expr
convertLiftedExpr (LIR.Bind _ arg k _) =
  bind <$> convertLiftedExpr arg <*> convertLiftedExpr k

-- TODO: unify with LIR.Var case
lookupVarPat :: LIR.VarPat -> Converter Agda.Name
lookupVarPat (LIR.VarPat _ name _) = do
  valueName <- inEnv $ lookupEntry IR.ValueScope name
  freshName <- inEnv $ lookupEntry IR.FreshScope name
  maybe (fail "") (return . Agda.unqualify . entryAgdaIdent)
    $   valueName
    <|> freshName
