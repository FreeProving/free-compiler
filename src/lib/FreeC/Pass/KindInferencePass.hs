
-- | This module contains a compiler pass that checks if all type constructors
--   in type expressions are fully applied and type variables are not applied.
--
--   For simplification, all type variables have kind @*@. Therefore, all type
--   constructors must be fully applied, so partial application of type
--   constructors is not allowed. This pass also checks that type variables and
--   function types do not occur on the left hand side of a type application.
--   If a type expression is found that does not match this rules, a fatal
--   error is thrown. For simplification, a type expression that satisfies all
--   of these rules is called kind-correct.
--
--   = Example
--
--   The following module contains three invalid definitions
--
--   > module Failures where
--   >
--   > data MyList a = MyNil | MyCons a (MyList a)
--   >
--   > fail1 :: MyList (MyList a a) -> Integer
--   > fail1 x = 42
--   >
--   > fail2 :: a a -> Integer
--   > fail2 x = 42
--   >
--   > fail3 :: MyList -> Integer
--   > fail3 x = 42
--
--   = Specification
--
--   == Preconditions
--
--   The environment must contain all type declarations that are used in the
--   module
--
--   == Translations
--
--   The AST is not changed. It is checked if all type constructor applications
--   have the right number of arguments. It is also checked whether there are
--   type variables or function types on the left-hand side of type
--   applications. In these cases, a fatal error is thrown. Otherwise, the
--   pass finishes with the given module unchanged.
--
--   == Postcondition
--
--   All type constructors in type expressions are applied to the correct
--   number of arguments and there are no type variables or function types on
--   the left-hand side of type applications. 
module FreeC.Pass.KindInferencePass
  ( kindInferencePass
  )
where

import           Control.Monad                  ( when )
import           Data.Maybe                     ( fromMaybe )

import           FreeC.Environment              ( lookupArity )
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pass
import           FreeC.Pretty                   ( showPretty )

-- | A compiler pass that checks wheter there are type applications with type
--   variables or function types on the left-hand side in the module and checks
--   whether all type construcors in the module are fully applied.
kindInferencePass :: Pass IR.Module
kindInferencePass m@(IR.Module _ _ _ typeDecls typeSigs _ funcDecls) = do
  checkTypeDecls typeDecls
  checkTypeSigs typeSigs
  checkFuncDecls funcDecls
  return m

-- |
checkMaybeTypeSchema :: Maybe IR.TypeSchema -> Converter ()
checkMaybeTypeSchema Nothing  = return ()
checkMaybeTypeSchema (Just x) = checkTypeSchema x

-- | Checks whether an optional type expression is kind correct in case the
--   type expression is present
checkMaybeType :: Maybe IR.Type -> Converter ()
checkMaybeType Nothing  = return ()
checkMaybeType (Just x) = checkType x

-- | Checks whether all type declarations have kind-correct type expressions
checkTypeDecls :: [IR.TypeDecl] -> Converter ()
checkTypeDecls = mapM_ checkTypeDecl

-- | Checks whether all type signatures have kind-correct types
checkTypeSigs :: [IR.TypeSig] -> Converter ()
checkTypeSigs = mapM_ checkTypeSig

-- | Checks whether all function declarations have kind-correct type
--   annotations
checkFuncDecls :: [IR.FuncDecl] -> Converter ()
checkFuncDecls = mapM_ checkFuncDecl

-- | Checks whether all type expressions in a type declaration are correct
checkTypeDecl :: IR.TypeDecl -> Converter ()
checkTypeDecl (IR.DataDecl    _ _ _ conDecls) = mapM_ checkConDecl conDecls
checkTypeDecl (IR.TypeSynDecl _ _ _ typ     ) = checkType typ

-- | Checks whether the arguments of a constructor declaration are kind-correct
checkConDecl :: IR.ConDecl -> Converter ()
checkConDecl (IR.ConDecl _ _ types) = mapM_ checkType types

-- | Checks whether the type schema in a type signature is kind-correct
checkTypeSig :: IR.TypeSig -> Converter ()
checkTypeSig (IR.TypeSig _ _ typeSchema) = checkTypeSchema typeSchema

-- | Checks whether a given type schema is kind-correct
checkTypeSchema :: IR.TypeSchema -> Converter ()
checkTypeSchema (IR.TypeSchema _ _ typ) = checkType typ

-- | Checks whether a function declaration has kind-correct type annotations
checkFuncDecl :: IR.FuncDecl -> Converter ()
checkFuncDecl (IR.FuncDecl _ _ _ varPats retType rhs) = do
  checkVarPats varPats
  checkMaybeType retType
  checkExpr rhs
  return ()

-- | Checks whether all type annotations in an expression are kind-correct
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

-- | Performs @checkAlt@ on all elements of the given list.
checkAlts :: [IR.Alt] -> Converter ()
checkAlts = mapM_ checkAlt

-- | Checks whether the variable patterns have correct type annotations and the
--   expression has kind-correct type annotations
checkAlt :: IR.Alt -> Converter ()
checkAlt (IR.Alt _ _ varPats rhs) = do
  checkVarPats varPats
  checkExpr rhs

-- | Performs @checkVarPat@ on all elems in the given list.
checkVarPats :: [IR.VarPat] -> Converter ()
checkVarPats = mapM_ checkVarPat

-- | Checks whether the type annotation of a variable pattern is kind-correct.
checkVarPat :: IR.VarPat -> Converter ()
checkVarPat (IR.VarPat _ _ typ) = checkMaybeType typ

-- | Checks whether a type is kind-correct
checkType :: IR.Type -> Converter ()
checkType = checkCorrectArities

-- | Checks if all type constructors have the correct number of arguments
checkCorrectArities :: IR.Type -> Converter ()
checkCorrectArities = checkCorrectArities' 0

-- | Helper function for @checkCorrectArities@
checkCorrectArities' :: Int -> IR.Type -> Converter ()
checkCorrectArities' depth (IR.TypeVar srcSpan varId) =
  when (depth /= 0)
    $  reportFatal
    $  Message srcSpan Error
    $  "Type variable "
    ++ varId
    ++ " occurs on left-hand side of type application"
checkCorrectArities' depth (IR.TypeCon srcSpan ident) = do
  arity <- inEnv $ fromMaybe (-1) . lookupArity IR.TypeScope ident
  when (arity /= depth)
    $  reportFatal
    $  Message srcSpan Error
    $  "Type constructor "
    ++ showPretty ident
    ++ " is applied to wrong number of arguments: expected "
    ++ show arity
    ++ " but was "
    ++ show depth
checkCorrectArities' depth (IR.TypeApp _ lhs rhs) = do
  checkCorrectArities' (depth + 1) lhs
  checkCorrectArities rhs
checkCorrectArities' depth (IR.FuncType srcSpan lhs rhs)
  | depth /= 0
  = reportFatal
    $ Message srcSpan Error
    $ "Function type occurs on left-hand side of type application"
  | otherwise
  = do
    checkCorrectArities lhs
    checkCorrectArities rhs
