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

checkTypeDecls :: Monad m => m IR.TypeDecl -> Converter ()
checkTypeDecls = mapM_ checkTypeDecl

checkTypeSigs :: Monad m => m IR.TypeSig -> Converter ()
checkTypeSigs = mapM_ checkTypeSig

checkFuncDecls :: Monad m => m IR.FuncDecl -> Converter ()
checkFuncDecls = mapM_ checkFuncDecl

checkTypes :: Monad m => m IR.Type -> Converter ()
checkTypes = mapM_ containsLeftTypeVars

checkTypeDecl :: IR.TypeDecl -> Converter ()
checkTypeDecl (IR.DataDecl    _ _ _ conDecls) = mapM_ checkConDecl conDecls
checkTypeDecl (IR.TypeSynDecl _ _ _ typ     ) = containsLeftTypeVars typ

checkConDecl :: IR.ConDecl -> Converter ()
checkConDecl (IR.ConDecl _ _ types) = mapM_ containsLeftTypeVars types

checkTypeSig :: IR.TypeSig -> Converter ()
checkTypeSig (IR.TypeSig _ _ typeSchema) = checkTypeSchema typeSchema

checkTypeSchema :: IR.TypeSchema -> Converter ()
checkTypeSchema (IR.TypeSchema _ _ typ) = containsLeftTypeVars typ

checkFuncDecl :: IR.FuncDecl -> Converter ()
checkFuncDecl (IR.FuncDecl _ _ _ varPats retType rhs) = do
  checkVarPats varPats
  checkTypes retType
  checkExpr rhs
  return ()

checkExpr :: IR.Expr -> Converter ()
checkExpr (IR.Con _ _ typeSchema      ) = mapM_ checkTypeSchema typeSchema
checkExpr (IR.Var _ _ typeSchema      ) = mapM_ checkTypeSchema typeSchema
checkExpr (IR.App _ lhs rhs typeSchema) = do
  checkExpr lhs
  checkExpr rhs
  mapM_ checkTypeSchema typeSchema
checkExpr (IR.TypeAppExpr _ lhs rhs typeSchema) = do
  checkExpr lhs
  containsLeftTypeVars rhs
  mapM_ checkTypeSchema typeSchema
checkExpr (IR.If _ cond thenExp elseExp typeSchema) = do
  checkExpr cond
  checkExpr thenExp
  checkExpr elseExp
  mapM_ checkTypeSchema typeSchema
checkExpr (IR.Case _ scrutinee alts typeSchema) = do
  checkExpr scrutinee
  checkAlts alts
  mapM_ checkTypeSchema typeSchema
checkExpr (IR.Undefined _ typeSchema      ) = mapM_ checkTypeSchema typeSchema
checkExpr (IR.ErrorExpr  _ _ typeSchema   ) = mapM_ checkTypeSchema typeSchema
checkExpr (IR.IntLiteral _ _ typeSchema   ) = mapM_ checkTypeSchema typeSchema
checkExpr (IR.Lambda _ args rhs typeSchema) = do
  checkVarPats args
  checkExpr rhs
  mapM_ checkTypeSchema typeSchema

checkAlts :: Monad m => m IR.Alt -> Converter ()
checkAlts = mapM_ checkAlt

checkAlt :: IR.Alt -> Converter ()
checkAlt (IR.Alt _ _ varPats rhs) = do
  checkVarPats varPats
  checkExpr rhs

checkVarPats :: Monad m => m IR.VarPat -> Converter ()
checkVarPats = mapM_ checkVarPat

checkVarPat :: IR.VarPat -> Converter ()
checkVarPat (IR.VarPat _ _ typ) = checkTypes typ


containsLeftTypeVars :: IR.Type -> Converter ()
containsLeftTypeVars (IR.TypeVar _ _) = return ()
containsLeftTypeVars (IR.TypeCon _ _) = return ()
containsLeftTypeVars (IR.TypeApp _ (IR.TypeVar srcSpan varId) _) =
  reportFatal
    $  Message srcSpan Error
    $  "Type variable "
    ++ varId
    ++ " occurs on right-hand"
    ++ " side of type application"
containsLeftTypeVars (IR.TypeApp _ lhs _) = do
  containsLeftTypeVars lhs
containsLeftTypeVars (IR.FuncType _ lhs rhs) = do
  containsLeftTypeVars lhs
  containsLeftTypeVars rhs
