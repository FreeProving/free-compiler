-- | This module contains a compiler pass that analyses the right-hand sides of
--   function declaration and introduces @let@-expression with new variables
--   for each variable that occurs more than once on the right-hand sides.
--
--   = Examples
--
--   == Example 1
--
--   > twice :: Integer -> Integer
--   > twice (x :: Integer) = x + x
--
--   Should be transformed into
--
--   > twice :: Integer -> Maybe Integer
--   > twice (x :: Integer) = let (y :: Integer) = x in y + y
--
--   == Example 2
--
--   > twiceMaybe :: Maybe Integer -> Maybe Integer
--   > twiceMaybe (mx :: Maybe Integer) = case (mx :: Maybe Integer) of {
--   >     Nothing -> Nothing;
--   >     Just x  -> Just (x + x)
--   >   }
--
--   Should be transformed into
--
--   > twiceMaybe :: Maybe Integer -> Maybe Integer
--   > twiceMaybe (mx :: Maybe Integer) = case (mx :: Maybe Integer) of {
--   >     Nothing -> Nothing;
--   >     Just x  -> let y = x in Just (y + y)
--   >   }
--
--
--   = Specification
--
--   == Preconditions
--
--   There are no special requirements.
--
--   == Translation
--
--   All shared variables on right-hand sides of function declarations are made
--   explicit by introducing @let@-expressions.

module FreeC.Pass.SharingAnalysisPass ( sharingAnaylsisPass ) where

import           Control.Monad             ( foldM, mplus )
import           Data.Map.Strict           ( Map )
import qualified Data.Map.Strict        as Map

import           FreeC.Environment.Fresh   ( freshHaskellQName )
import           FreeC.Environment.Renamer ( renameAndDefineVar )
import qualified FreeC.IR.Syntax        as IR
import           FreeC.IR.Subst
import           FreeC.IR.SrcSpan
import           FreeC.Monad.Converter
import           FreeC.Pass

-- | Checks all function declarations if they contain variables that occur
--   multiple times on the same right-hand side.
--   If that is the case, a @let@-expression is introduced that binds the
--   variables to fresh ones and replaces the occurrences with the newly
--   introduced variable.
sharingAnaylsisPass :: Pass IR.Module
sharingAnaylsisPass
    (IR.Module srcSpan name imports typeDecls typeSigs pragmas funcDecls) = do
        funcDecls' <- mapM analyseSharingDecl (funcDecls)
        return (IR.Module srcSpan name imports typeDecls typeSigs pragmas
                funcDecls')

-- | Checks a function declaration if it contains a variable that occurs
--   multiple times on the right-hand side.
--   If that is the case, a @let@-expression is introduced.
analyseSharingDecl :: IR.FuncDecl -> Converter IR.FuncDecl
analyseSharingDecl (IR.FuncDecl srcSpan ident typeArgs args returnType rhs) = do
    let varList = (map (\p -> ( fst p, snd $ snd p )) . filter
                   ((> 1) . fst . snd) . Map.toList . countVarNames) rhs
    rhs' <- buildLet rhs varList
    return (IR.FuncDecl srcSpan ident typeArgs args returnType rhs')

-- | Builds a @let@-expression from the given expression and variable names.
--
--   Computes @let@-bindings from the given variables, composes the resulting
--   substitutions and applies the substitution on the expression.
buildLet
    :: IR.Expr -> [ ( IR.VarName, Maybe IR.TypeScheme ) ] -> Converter IR.Expr
buildLet expr []   = return expr
buildLet expr vars = do
    let srcSpan = IR.exprSrcSpan expr
    ( binds, substs ) <- buildBinds srcSpan vars
    return (IR.Let srcSpan binds (applySubst (composeSubsts substs) expr)
            (IR.exprTypeScheme expr))

-- | Converts the list containing variables into @let@-bindings where
--   the variable pattern is a fresh variable and the right-hand side is
--   a variable that occurred multiple times on right hand sides.
--
--   Also computes substitutions mapping given variables to fresh variables.
--   Returns the generated let-bindings and the substitutions.
buildBinds :: SrcSpan -> [ ( IR.VarName, Maybe IR.TypeScheme ) ]
    -> Converter ( [ IR.Bind ], [ Subst IR.Expr ] )
buildBinds srcSpan = foldM buildBind ( [], [] )
  where
    buildBind :: ( [ IR.Bind ], [ Subst IR.Expr ] )
        -> ( IR.VarName, Maybe IR.TypeScheme )
        -> Converter ( [ IR.Bind ], [ Subst IR.Expr ] )
    buildBind ( binds, substs ) ( varName, varTypeScheme ) = do
        varName' <- freshHaskellQName varName
        let subst = singleSubst' varName (\s -> IR.Var s varName' varTypeScheme)
            -- This type scheme has wrong source span information.
            rhs = IR.Var srcSpan varName varTypeScheme
            Just varPatIdent = IR.identFromQName varName'
            varPatType = fmap IR.typeSchemeType varTypeScheme
            varPat = IR.VarPat srcSpan varPatIdent varPatType False
            bind = IR.Bind srcSpan varPat rhs
        _ <- renameAndDefineVar srcSpan False varPatIdent varPatType
        return ( bind : binds, subst : substs )

-- | Counts all variable names on right-hand sides of expression.
--
--   If a variable is annotated with a type scheme the annotation is introduced
--   into the map as well.
countVarNames :: IR.Expr -> Map IR.VarName ( Integer, Maybe IR.TypeScheme )
countVarNames IR.Con {} = Map.empty
countVarNames (IR.Var _ varName maybeTypeScheme)
    = Map.singleton varName ( 1, maybeTypeScheme )
countVarNames (IR.App _ lhs rhs _)
    = countVarNames lhs `mergeMap` countVarNames rhs
countVarNames (IR.TypeAppExpr _ lhs _ _) = countVarNames lhs
countVarNames (IR.If _ e1 e2 e3 _) = (countVarNames e1)
    `mergeMap` (countVarNames e2) `mergeMap` countVarNames e3
countVarNames (IR.Case _ e alts _) = countVarNames e `mergeMap` foldr mergeMap
    Map.empty (map (countVarNames . IR.altRhs) alts)
countVarNames IR.Undefined {} = Map.empty
countVarNames IR.ErrorExpr {} = Map.empty
countVarNames IR.IntLiteral {} = Map.empty
countVarNames (IR.Lambda _ _ rhs _) = countVarNames rhs
countVarNames (IR.Let _ binds e _) = countVarNames e `mergeMap` foldr mergeMap
    Map.empty (map (countVarNames . IR.bindExpr) binds)

mergeMap :: Map IR.VarName ( Integer, Maybe IR.TypeScheme )
    -> Map IR.VarName ( Integer, Maybe IR.TypeScheme )
    -> Map IR.VarName ( Integer, Maybe IR.TypeScheme )
mergeMap = Map.unionWith (\p1 p2 -> ( fst p1 + fst p2, snd p1 `mplus` snd p2 ))
