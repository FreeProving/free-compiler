module FreeC.Backend.Agda.Converter.Expr
  ( convertExpr
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

convertExpr :: LIR.Expr -> Converter Agda.Expr
convertExpr (LIR.Con _ _ _) = fail "Missing case for constructors!"
convertExpr (LIR.SmartCon srcSpan name _) =
  Agda.Ident <$> lookupAgdaSmartIdentOrFail srcSpan name
convertExpr (LIR.Var _ name _) = do
  valueName <- inEnv $ lookupEntry IR.ValueScope name
  freshName <- inEnv $ lookupEntry IR.FreshScope name
  -- Adding an alternative instance for @ReporterT@ and @ConverterT@ would allow us to use @lookupOrFail@ functions.
  return $ Agda.Ident $ entryAgdaIdent $ fromJust $ valueName <|> freshName
convertExpr (LIR.App _ expr _ _ args _) =
  foldl Agda.app <$> convertExpr expr <*> mapM convertExpr args
convertExpr (LIR.If _ cond true false _) =
  Agda.ite <$> convertExpr cond <*> convertExpr true <*> convertExpr false
convertExpr (LIR.Case _ _ _ _       ) = undefined
convertExpr (LIR.Undefined _ _      ) = undefined
convertExpr (LIR.ErrorExpr  _ _   _ ) = undefined
convertExpr (LIR.IntLiteral _ val _ ) = return $ Agda.intLiteral val
convertExpr (LIR.Lambda _ args rhs _) = do
  Agda.lambda <$> mapM lookupVarPat args <*> convertExpr rhs
convertExpr (LIR.Pure _ expr _ ) = generatePure <$> convertExpr expr
convertExpr (LIR.Bind _ arg k _) = bind <$> convertExpr arg <*> convertExpr k

-- TODO: unify with LIR.Var case
lookupVarPat :: LIR.VarPat -> Converter Agda.Name
lookupVarPat (LIR.VarPat _ name _) = do
  valueName <- inEnv $ lookupEntry IR.ValueScope name
  freshName <- inEnv $ lookupEntry IR.FreshScope name
  maybe (fail "") (return . Agda.unqualify . entryAgdaIdent)
    $   valueName
    <|> freshName
