module FreeC.Pass.KindInferencePass
  ( kindInferencePass
  )
where

import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pass
import           FreeC.Pretty

kindInferencePass :: Pass IR.Module
kindInferencePass m@(IR.Module _ _ _ typeDecls typeSigs _ funcDecls) = do
  checkTypeDecls typeDecls
  checkTypeSigs typeSigs
  checkFuncDecls funcDecls
  return m

checkMaybeTypeSchema :: Maybe IR.TypeSchema -> Converter ()
checkMaybeTypeSchema Nothing  = return ()
checkMaybeTypeSchema (Just x) = checkTypeSchema x

checkMaybeType :: Maybe IR.Type -> Converter ()
checkMaybeType Nothing  = return ()
checkMaybeType (Just x) = checkType x

checkTypeDecls :: [IR.TypeDecl] -> Converter ()
checkTypeDecls = mapM_ checkTypeDecl

checkTypeSigs :: [IR.TypeSig] -> Converter ()
checkTypeSigs = mapM_ checkTypeSig

checkFuncDecls :: [IR.FuncDecl] -> Converter ()
checkFuncDecls = mapM_ checkFuncDecl

checkTypeDecl :: IR.TypeDecl -> Converter ()
checkTypeDecl (IR.DataDecl    _ _ _ conDecls) = mapM_ checkConDecl conDecls
checkTypeDecl (IR.TypeSynDecl _ _ _ typ     ) = checkType typ

checkConDecl :: IR.ConDecl -> Converter ()
checkConDecl (IR.ConDecl _ _ types) = mapM_ checkType types

checkTypeSig :: IR.TypeSig -> Converter ()
checkTypeSig (IR.TypeSig _ _ typeSchema) = checkTypeSchema typeSchema

checkTypeSchema :: IR.TypeSchema -> Converter ()
checkTypeSchema (IR.TypeSchema _ _ typ) = checkType typ

checkFuncDecl :: IR.FuncDecl -> Converter ()
checkFuncDecl (IR.FuncDecl _ _ _ varPats retType rhs) = do
  checkVarPats varPats
  checkMaybeType retType
  checkExpr rhs
  return ()

checkExpr :: IR.Expr -> Converter ()
checkExpr (IR.Con _ _ typeSchema      ) = checkMaybeTypeSchema typeSchema
checkExpr (IR.Var _ _ typeSchema      ) = checkMaybeTypeSchema typeSchema
checkExpr (IR.App _ lhs rhs typeSchema) = do
  checkExpr lhs
  checkExpr rhs
  checkMaybeTypeSchema typeSchema
checkExpr (IR.TypeAppExpr _ lhs rhs typeSchema) = do
  checkExpr lhs
  checkType rhs
  checkMaybeTypeSchema typeSchema
checkExpr (IR.If _ cond thenExp elseExp typeSchema) = do
  checkExpr cond
  checkExpr thenExp
  checkExpr elseExp
  checkMaybeTypeSchema typeSchema
checkExpr (IR.Case _ scrutinee alts typeSchema) = do
  checkExpr scrutinee
  checkAlts alts
  checkMaybeTypeSchema typeSchema
checkExpr (IR.Undefined _ typeSchema      ) = checkMaybeTypeSchema typeSchema
checkExpr (IR.ErrorExpr  _ _ typeSchema   ) = checkMaybeTypeSchema typeSchema
checkExpr (IR.IntLiteral _ _ typeSchema   ) = checkMaybeTypeSchema typeSchema
checkExpr (IR.Lambda _ args rhs typeSchema) = do
  checkVarPats args
  checkExpr rhs
  checkMaybeTypeSchema typeSchema

checkAlts :: [IR.Alt] -> Converter ()
checkAlts = mapM_ checkAlt

checkAlt :: IR.Alt -> Converter ()
checkAlt (IR.Alt _ _ varPats rhs) = do
  checkVarPats varPats
  checkExpr rhs

checkVarPats :: [IR.VarPat] -> Converter ()
checkVarPats = mapM_ checkVarPat

checkVarPat :: IR.VarPat -> Converter ()
checkVarPat (IR.VarPat _ _ typ) = checkMaybeType typ

checkType :: IR.Type -> Converter ()
checkType typ = do
                 containsLeftTypeVars typ
                 checkCorrectArities typ


checkCorrectArities :: IR.Type -> Converter ()
checkCorrectArities = checkCorrectArities' 0 -- to be implemented

checkCorrectArities' :: Int -> IR.Type -> Converter ()
checkCorrectArities' depth (IR.TypeVar srcSpan varId) = do
  if depth == 0 then
    return ()
  else do
        reportFatal $ Message srcSpan Error
                    $ "Type variable "
                    ++ varId 
                    ++ " occurs on left-hand side of type application"
checkCorrectArities' depth (IR.TypeCon srcSpan ident) = undefined
checkCorrectArities' depth (IR.TypeApp _ lhs rhs) = do
  checkCorrectArities' (depth + 1) lhs
  checkCorrectArities rhs
checkCorrectArities' depth (IR.FuncType srcSpan lhs rhs)
  | depth /= 0 = reportFatal
                 $ Message srcSpan Error
                 $ "Function type occurs on left-hand side of type application"
  | otherwise  = do
                   checkCorrectArities lhs
                   checkCorrectArities rhs


containsLeftTypeVars :: IR.Type -> Converter ()
containsLeftTypeVars (IR.TypeVar _ _) = return ()
containsLeftTypeVars (IR.TypeCon _ _) = return ()
containsLeftTypeVars (IR.TypeApp _ (IR.TypeVar srcSpan varId) _) =
  reportFatal
    $  Message srcSpan Error
    $  "Type variable "
    ++ varId
    ++ " occurs on left-hand"
    ++ " side of type application"
containsLeftTypeVars (IR.TypeApp _ lhs rhs) = do
  containsLeftTypeVars lhs
  containsLeftTypeVars rhs
containsLeftTypeVars (IR.FuncType _ lhs rhs) = do
  containsLeftTypeVars lhs
  containsLeftTypeVars rhs
