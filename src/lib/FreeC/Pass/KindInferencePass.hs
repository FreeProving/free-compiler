module Freec.Pass.KindInferencePass
  ()
where

import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pass
import           FreeC.Pretty

kindInferencePass :: Pass IR.Module
kindInferencePass (Module _ _ _ typeDecls typeSigs  _ funcDecls ) = do
  checkTypeDecls typeDecls
  checkTypeSigs typeSigs
  checkFuncDecls funcDecls

checkTypeDecls :: Monad m => m IR.TypeDecl -> Converter ()
checkTypeDecls typeDecls = mapM_ checkTypeDecl typeDecls

checkTypeSigs :: Monad m => m IR.TypeSig -> Converter ()
checkTypeSigs typeSigs = mapM_ checkTypeSig typeSigs

checkFuncDecls :: Monad m => m IR.FuncDecl -> Converter ()
checkFuncDecls funcDecls = mapM_ checkFuncDecl funcDecls

checkTypes :: Monad m => m IR.Type -> Converter ()
checkTypes types = mapM_ containsLeftTypeVars types

checkTypeDecl :: IR.TypeDecl -> Converter ()
checkTypeDecl (DataDecl _ _ _ conDecls) = mapM_ checkConDecl conDecls
checkTypeDecl (TypeSynDecl _ _ _ typ) = containsLeftTypeVars typ

checkConDecl :: IR.ConDecl -> Converter ()
checkConDecl (ConDecl _ _ types) = mapM_ containsLeftTypeVars types

checkTypeSig :: IR.TypeSig -> Converter ()
checkTypeSig (TypeSig _ _ typeSchema) = checkTypeSchema typeSchema

checkTypeSchema :: IR.TypeSchema -> Converter ()
checkTypeSchema (TypeSchema _ _ typ) = containsLeftTypeVars typ

checkFuncDecl :: IR.FuncDecl -> Converter ()
checkFuncDecl (_ _ _ varPats retType rhs) = do
  checkVarPats varPats
  checkTypes retType
  checkExpr rhs
  return ()

checkExpr :: IR.Expr -> Converter ()
checkExpr (Con _ _ typeSchema) = mapM_ checkTypeSchema typeSchema
checkExpr (Var _ _ typeSchema) = mapM_ checkTypeSchema typeSchema
checkExpr (App _ lhs rhs typeSchema) = do
  checkExpr lhs
  checkExpr rhs
  mapM_ checkTypeSchema typeSchema
  return ()
checkExpr (TypeAppExpr _ lhs rhs typeSchema) = do
  checkExpr lhs
  containsLeftTypeVars rhs
  mapM_ checkTypeSchema typeSchema
  return ()
checkExpr (If _ cond thenExp elseExp typeSchema) = do
  checkExpr cond
  checkExpr thenExp
  checkExpr elseExp
  mapM_ checkTypeSchema typeSchema
  return ()
checkExpr (Case _ scrutinee alts typeSchema) = do
  checkExpr scrutinee
  checkAlts alts
  mapM_ checkTypeSchema typeSchema
  return ()
checkExpr (Undefined _ typeSchema) = mapM_ checkTypeSchema typeSchema
checkExpr (ErrorExpr _ _ typeSchema) = mapM_ checkTypeSchema typeSchema
checkExpr (IntLiteral _ _ typeSchema) = mapM_ checkTypeSchema typeSchema
checkExpr (Lambda _ args rhs typeSchema) = do
  checkVarPats args
  checkExpr rhs
  mapM_ checkTypeSchema typeSchema
  return ()

checkVarPats :: Monad m => m IR.VarPat -> Converter ()
checkVarPats varPats = mapM_ checkVarPat varPats

checkVarPat :: VarPat -> Converter ()
checkVarPat (VarPat _ _ typ) = checkTypes typ


containsLeftTypeVars :: IR.Type -> Converter ()
containsLeftTypeVars (TypeVar _ _) = return ()
containsLeftTypeVars (TypeCon _ _) = return ()
containsLeftTypeVars (TypeApp _ (TypeVar srcSpan varId) _) =
  reportFatal
    $  Message srcSpan Error
    $  "Type variable "
    ++ varid
    ++ " occurs on right-hand"
    ++ " side of type application"
containsLeftTypeVars (TypeApp _ lhs _) = do
  containsLeftTypeVars lhs
containsLeftTypeVars (FuncType _ lhs rhs) = do
  containsLeftTypeVars lhs
  containsLeftTypeVars rhs
