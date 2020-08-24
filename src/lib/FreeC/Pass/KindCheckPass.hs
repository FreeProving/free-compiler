-- | This module contains a compiler pass that checks if all type constructors
--   in type expressions are fully applied and type variables are not applied.
--
--   For simplification, all type variables have kind @*@. Therefore, all type
--   constructors must be fully applied, so partial application of type
--   constructors is not allowed. This pass also checks that type variables and
--   function types do not occur on the left-hand side of a type application.
--   If a type expression is found that does not match this rules, a fatal
--   error is reported. For simplification, a type expression that satisfies all
--   of these rules is called kind-correct.
--
--   = Example
--
--   The following module contains three invalid definitions.
--
--   > module Failures where
--   >
--   > data MyList a = MyNil | MyCons a (MyList a)
--   >
--   > -- Invalid because 'MyList' is applied to 2 arguments.
--   > fail1 :: MyList (MyList a a) -> Integer
--   > fail1 x = 42
--   >
--   > -- Invalid because type variable 'a' is on the right-hand side of a type
--   > -- application.
--   > fail2 :: a a -> Integer
--   > fail2 x = 42
--   >
--   > -- Fails because 'MyList' is applied to no arguments.
--   > fail3 :: MyList -> Integer
--   > fail3 x = 42
--
--   = Specification
--
--   == Preconditions
--
--   The environment must contain entries for all type constructors that are
--   used in the module.
--
--   == Translations
--
--   The AST is not changed. It is checked if all type constructor applications
--   have the right number of arguments. It is also checked whether there are
--   type variables or function types on the left-hand side of type
--   applications. In these cases, a fatal error is reported. Otherwise, the
--   pass finishes with the given module unchanged.
--
--   == Postcondition
--
--   All type constructors in type expressions are applied to the correct
--   number of arguments and there are no type variables or function types on
--   the left-hand side of type applications.
module FreeC.Pass.KindCheckPass
  ( kindCheckPass
    -- * Testing Interface
  , checkType
  ) where

import           Control.Monad         ( when )
import           Data.Maybe            ( fromMaybe )

import           FreeC.Environment     ( lookupArity )
import qualified FreeC.IR.Syntax       as IR
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pass
import           FreeC.Pretty          ( showPretty )

-- | A compiler pass that checks whether there are type applications with type
--   variables or function types on the left-hand side in the module and checks
--   whether all type construcors in the module are fully applied.
kindCheckPass :: Pass IR.Module IR.Module
kindCheckPass m@(IR.Module _ _ _ typeDecls typeSigs _ funcDecls) = do
  mapM_ checkTypeDecl typeDecls
  mapM_ checkTypeSig typeSigs
  mapM_ checkFuncDecl funcDecls
  return m

-- | Checks whether all type expressions in a type declaration are correct.
checkTypeDecl :: IR.TypeDecl -> Converter ()
checkTypeDecl (IR.DataDecl _ _ _ conDecls)    = mapM_ checkConDecl conDecls
checkTypeDecl (IR.TypeSynDecl _ _ _ typeExpr) = checkType typeExpr

-- | Checks whether the arguments of a constructor declaration are kind-correct.
checkConDecl :: IR.ConDecl -> Converter ()
checkConDecl (IR.ConDecl _ _ types) = mapM_ checkType types

-- | Checks whether the type scheme in a type signature is kind-correct.
checkTypeSig :: IR.TypeSig -> Converter ()
checkTypeSig (IR.TypeSig _ _ typeScheme) = checkTypeScheme typeScheme

-- | Checks whether a given type scheme is kind-correct.
checkTypeScheme :: IR.TypeScheme -> Converter ()
checkTypeScheme (IR.TypeScheme _ _ typeExpr) = checkType typeExpr

-- | Checks whether a function declaration has kind-correct type annotations.
checkFuncDecl :: IR.FuncDecl -> Converter ()
checkFuncDecl (IR.FuncDecl _ _ _ varPats retType rhs) = do
  mapM_ checkVarPat varPats
  mapM_ checkType retType
  checkExpr rhs

-- | Checks whether all type annotations in an expression are kind-correct.
checkExpr :: IR.Expr -> Converter ()
checkExpr (IR.Con _ _ typeScheme)
  = mapM_ checkTypeScheme typeScheme
checkExpr (IR.Var _ _ typeScheme)
  = mapM_ checkTypeScheme typeScheme
checkExpr (IR.App _ lhs rhs typeScheme)               = do
  checkExpr lhs
  checkExpr rhs
  mapM_ checkTypeScheme typeScheme
checkExpr (IR.TypeAppExpr _ lhs rhs typeScheme)       = do
  checkExpr lhs
  checkType rhs
  mapM_ checkTypeScheme typeScheme
checkExpr (IR.If _ cond thenExpr elseExpr typeScheme) = do
  checkExpr cond
  checkExpr thenExpr
  checkExpr elseExpr
  mapM_ checkTypeScheme typeScheme
checkExpr (IR.Case _ scrutinee alts typeScheme)       = do
  checkExpr scrutinee
  mapM_ checkAlt alts
  mapM_ checkTypeScheme typeScheme
checkExpr (IR.Undefined _ typeScheme)
  = mapM_ checkTypeScheme typeScheme
checkExpr (IR.ErrorExpr _ _ typeScheme)
  = mapM_ checkTypeScheme typeScheme
checkExpr (IR.IntLiteral _ _ typeScheme)
  = mapM_ checkTypeScheme typeScheme
checkExpr (IR.Lambda _ args rhs typeScheme)           = do
  mapM_ checkVarPat args
  checkExpr rhs
  mapM_ checkTypeScheme typeScheme
checkExpr (IR.Let _ binds expr typeScheme)            = do
  mapM_ checkBind binds
  checkExpr expr
  mapM_ checkTypeScheme typeScheme

-- | Checks whether the variable patterns have correct type annotations and the
--   expression has kind-correct type annotations.
checkAlt :: IR.Alt -> Converter ()
checkAlt (IR.Alt _ _ varPats rhs) = do
  mapM_ checkVarPat varPats
  checkExpr rhs

-- | Checks whether the type annotation of a variable pattern is kind-correct.
checkVarPat :: IR.VarPat -> Converter ()
checkVarPat (IR.VarPat _ _ typeExpr _) = mapM_ checkType typeExpr

-- | Checks if all type constructors have the correct number of arguments.
checkType :: IR.Type -> Converter ()
checkType = checkType' 0

-- | Checks whether the variable patterns have correct type annotations and the
--   expression has kind-correct type annotations.
checkBind :: IR.Bind -> Converter ()
checkBind (IR.Bind _ varPat expr) = do
  checkVarPat varPat
  checkExpr expr

-- | Helper function for @checkType@. Uses a counter to count how many
--   arguments have already been applied.
checkType' :: Int -> IR.Type -> Converter ()
checkType' depth (IR.TypeVar srcSpan varId)    = when (depth /= 0)
  $ reportFatal
  $ Message srcSpan Error
  $ "Type variable "
  ++ varId
  ++ " occurs on left-hand side of type application."
checkType' depth (IR.TypeCon srcSpan ident)    = do
  arity <- inEnv $ fromMaybe (-1) . lookupArity IR.TypeScope ident
  when (arity /= depth)
    $ reportFatal
    $ Message srcSpan Error
    $ "Type constructor "
    ++ showPretty ident
    ++ " is applied to wrong number of arguments: Expected "
    ++ show arity
    ++ " but was "
    ++ show depth
    ++ "."
checkType' depth (IR.TypeApp _ lhs rhs)        = do
  checkType' (depth + 1) lhs
  checkType rhs
checkType' depth (IR.FuncType srcSpan lhs rhs)
  | depth /= 0 = reportFatal
    $ Message srcSpan Error
    $ "Function type occurs on left-hand side of type application."
  | otherwise = do
    checkType lhs
    checkType rhs
