module FreeC.Pass.CompletePatternPass
  ( completePatternPass
  )
where

import           Data.Maybe                     ( fromJust )

import           FreeC.Environment
import           FreeC.Environment.Entry
import qualified FreeC.IR.Syntax                   as IR
import           FreeC.IR.SrcSpan
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pass

-- | Checks that all functions of a given module have complete pattern matching.
--   The pattern matching is complete if there is exactly one case alternative
--   for each constructor of the corresponding type.
completePatternPass :: Pass IR.Module
completePatternPass ast = do
  mapM_ checkPatternFuncDecl (IR.modFuncDecls ast)
  return ast

checkPatternFuncDecl :: IR.FuncDecl -> Converter ()
checkPatternFuncDecl funcDecl = checkPatternExp (IR.funcDeclRhs funcDecl)
 where
  checkPatternExp :: IR.Expr -> Converter ()
  checkPatternExp (IR.Case srcSpan exprScrutinee exprAlts _) = do
    let mTau = IR.exprType (exprScrutinee)
    case getTypeConName (fromJust mTau) of-- fromJust safe because type is known
      Nothing -> failedPatternCheck srcSpan
      Just typeName -> do
        env <- getEnv
        case lookupEntry IR.TypeScope typeName env of
          Just entry | isDataEntry entry -> do
            let typeConNames = entryConsNames entry
            let altConNames = map (IR.conPatName . IR.altConPat) exprAlts
            if (all (\x -> elem x typeConNames) typeConNames
                && length typeConNames == length altConNames)
              then return ()
              else failedPatternCheck  srcSpan -- report fatal error
          _   -> failedPatternCheck srcSpan  -- report fatal error
  checkPatternExp (IR.App _ lhr rhs _) = checkPatternExp lhr >> checkPatternExp rhs
  checkPatternExp (IR.TypeAppExpr _ lhr _ _) = checkPatternExp lhr
  checkPatternExp (IR.If _ exprCond exprThen exprElse _) =
    checkPatternExp exprCond >> checkPatternExp exprThen >> checkPatternExp exprElse
  checkPatternExp (IR.Lambda _ _ lambdaRhs _) = checkPatternExp lambdaRhs
  checkPatternExp _ = return ()

  failedPatternCheck :: SrcSpan -> Converter ()
  failedPatternCheck srcSpan = reportFatal
    $ Message srcSpan Error
    $ "Incomplete pattern in function: "
    ++  stringFromName (IR.funcDeclName funcDecl)

  stringFromName :: IR.Name -> String
  stringFromName (IR.Ident s) = s
  stringFromName (IR.Symbol s) = s

  getTypeConName :: IR.Type -> Maybe IR.TypeConName
  getTypeConName (IR.TypeCon  _ typeConName) = Just typeConName
  getTypeConName (IR.TypeApp  _ typeAppLhs _ ) = getTypeConName typeAppLhs
    -- The type of the scrutinee shouldn't be function or a type var
  getTypeConName _ = Nothing
