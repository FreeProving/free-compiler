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
--   where @y@ is a fresh variable.
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
--   where @y@ is a fresh variable.
--
--   == Example 3
--
--   > two :: Integer
--   > two = let x = 1 in x + x
--
--   Should not be changed by the transformation.
--
--   = Specification
--
--   == Preconditions
--
--   There are no special requirements.
--
--   == Translation
--
--   First all subexpressions of each function declaration are checked for variables
--   occurring multiple times on the right hand sides of lambda abstractions or
--   @case@-expression alternatives. If found the variables are replaced by a
--   fresh variable and a @let@-binding is introduced binding the fresh variable
--   to the old one.
--
--   After all subexpressions are checked the right hand side of the function
--   declaration is checked as well.
--   Variables already bound by @let@-bindings are not counted.
--
--   == Postconditions
--
--   All shared variables on right-hand sides of function declarations are made
--   explicit by introducing @let@-expressions.
module FreeC.Pass.SharingAnalysisPass ( sharingAnaylsisPass ) where

import           Control.Monad           ( mapAndUnzipM )
import           Data.Map.Strict         ( Map )
import qualified Data.Map.Strict         as Map

import           FreeC.Environment.Fresh ( freshHaskellQName )
import           FreeC.IR.SrcSpan
import           FreeC.IR.Subst
import qualified FreeC.IR.Syntax         as IR
import           FreeC.Monad.Converter
import           FreeC.Pass

-- | Checks all function declarations if they contain variables that occur
--   multiple times on the same right-hand side.
--   If that is the case, a @let@-expression is introduced that binds the
--   variables to fresh ones and replaces the occurrences with the newly
--   introduced variable.
sharingAnaylsisPass :: Pass IR.Module IR.Module
sharingAnaylsisPass ast = do
  funcDecls' <- mapM analyseSharingDecl (IR.modFuncDecls ast)
  return ast { IR.modFuncDecls = funcDecls' }

-- | Checks a function declaration for @case@-expressions to introduce local
--   @let@-expressions and applies the transformation on the right-hand side.
analyseSharingDecl :: IR.FuncDecl -> Converter IR.FuncDecl
analyseSharingDecl (IR.FuncDecl srcSpan ident typeArgs args returnType rhs) = do
  rhs' <- analyseLocalSharing rhs
  rhs'' <- analyseSharingExpr rhs'
  return (IR.FuncDecl srcSpan ident typeArgs args returnType rhs'')

-- | Checks the expression and all right-hand sides of subexpressions
--   for shared variables that are introduced through @case@-alternatives
--   or lambda abstractions.
--
--   If a variable is shared, a @let@-expression that makes the sharing
--   explicit is introduced.
analyseLocalSharing :: IR.Expr -> Converter IR.Expr
analyseLocalSharing (IR.Case srcSpan expr alts typeScheme) = do
  expr' <- analyseLocalSharing expr
  alts' <- mapM analyseSharingAlt alts
  return (IR.Case srcSpan expr' alts' typeScheme)
 where
  analyseSharingAlt :: IR.Alt -> Converter IR.Alt
  analyseSharingAlt (IR.Alt altSrcSpan altConPat altVarPats altRhs) = do
    let varNames = map IR.varPatQName altVarPats
        varList  = (map fst
                    . filter ((> 1) . snd)
                    . Map.toList
                    . countVarNamesOnly varNames) altRhs
    altRhs' <- buildLet altRhs varList
    return (IR.Alt altSrcSpan altConPat altVarPats altRhs')
analyseLocalSharing (IR.Lambda srcSpan exprArgs rhs typeScheme) = do
  let varNames = map IR.varPatQName exprArgs
      varList  = (map fst
                  . filter ((> 1) . snd)
                  . Map.toList
                  . countVarNamesOnly varNames) rhs
  rhs' <- buildLet rhs varList
  return (IR.Lambda srcSpan exprArgs rhs' typeScheme)
analyseLocalSharing expr@IR.Con {} = return expr
analyseLocalSharing expr@IR.Undefined {} = return expr
analyseLocalSharing expr@IR.ErrorExpr {} = return expr
analyseLocalSharing expr@IR.Var {} = return expr
analyseLocalSharing expr@IR.IntLiteral {} = return expr
analyseLocalSharing (IR.Let srcSpan binds rhs typeScheme) = do
  binds' <- mapM analyseSharingBind binds
  rhs' <- analyseLocalSharing rhs
  return (IR.Let srcSpan binds' rhs' typeScheme)
 where
  analyseSharingBind :: IR.Bind -> Converter IR.Bind
  analyseSharingBind (IR.Bind bindSrcSpan bindVarPat bindRhs) = do
    bindRhs' <- analyseLocalSharing bindRhs
    return (IR.Bind bindSrcSpan bindVarPat bindRhs')
analyseLocalSharing (IR.If srcSpan e1 e2 e3 typeScheme) = do
  e1' <- analyseLocalSharing e1
  e2' <- analyseLocalSharing e2
  e3' <- analyseLocalSharing e3
  return (IR.If srcSpan e1' e2' e3' typeScheme)
analyseLocalSharing (IR.TypeAppExpr srcSpan lhs rhs typeScheme) = do
  lhs' <- analyseLocalSharing lhs
  return (IR.TypeAppExpr srcSpan lhs' rhs typeScheme)
analyseLocalSharing (IR.App srcSpan lhs rhs typeScheme) = do
  lhs' <- analyseLocalSharing lhs
  rhs' <- analyseLocalSharing rhs
  return (IR.App srcSpan lhs' rhs' typeScheme)

-- | Checks if an expression contains variables that occur
--   multiple times on the same right-hand side.
--   If that is the case, a @let@-expression is introduced that binds the
--   variables to fresh ones and replaces the occurrences with the newly
--   introduced variable.
analyseSharingExpr :: IR.Expr -> Converter IR.Expr
analyseSharingExpr expr = do
  let varList
        = (map fst . filter ((> 1) . snd) . Map.toList . countVarNamesExcept [])
        expr
  buildLet expr varList

-- | Builds a @let@-expression from the given expression and variable names.
--
--   Computes @let@-bindings from the given variables, composes the resulting
--   substitutions and applies the substitution on the expression.
buildLet :: IR.Expr -> [IR.VarName] -> Converter IR.Expr
buildLet expr []   = return expr
buildLet expr vars = do
  let srcSpan = IR.exprSrcSpan expr
  (binds, substs) <- buildBinds srcSpan vars
  return (IR.Let srcSpan binds (applySubst (composeSubsts substs) expr)
          (IR.exprTypeScheme expr))

-- | Converts the list containing variables into @let@-bindings where
--   the variable pattern is a fresh variable and the right-hand side is
--   a variable that occurred multiple times on right hand sides.
--
--   Also computes substitutions mapping given variables to fresh variables.
--   Returns the generated @let@-bindings and the substitutions.
buildBinds :: SrcSpan -> [IR.VarName] -> Converter ([IR.Bind], [Subst IR.Expr])
buildBinds srcSpan = mapAndUnzipM buildBind
 where
  buildBind :: IR.VarName -> Converter (IR.Bind, Subst IR.Expr)
  buildBind varName = do
    varName' <- freshHaskellQName varName
    let subst            = singleSubst' varName
          (\s -> IR.Var s varName' Nothing)
        rhs              = IR.Var srcSpan varName Nothing
        Just varPatIdent = IR.identFromQName varName'
        varPat           = IR.VarPat srcSpan varPatIdent Nothing False
        bind             = IR.Bind srcSpan varPat rhs
    return (bind, subst)

-- | Counts all variable names on right-hand sides of expression.
--   Shadowed variables and variables from the list are not counted.
--   Variables introduced on the left side of a @case@-alternative and @let@
--   expressions are not counted.
countVarNamesExcept :: [IR.VarName] -> IR.Expr -> Map IR.VarName Integer
countVarNamesExcept = countVarNamesWith (++) elem

-- | Counts all variable names on right-hand sides of expression that are also
--   contained by the given list.
--   Shadowed variables and variables from the list are not counted.
--   Variables introduced on the left side of a @case@-alternative and @let@
--   expressions are not counted.
countVarNamesOnly :: [IR.VarName] -> IR.Expr -> Map IR.VarName Integer
countVarNamesOnly = countVarNamesWith const notElem

-- | A generalized recursive counting for variables in expressions.
--   The first arguments is the function that is used to combine
--   the given list of variable names with variable names from left-hand sides
--   of @case@-alternatives or lambda abstractions.
--   The second argument is a predicate that determines if a variable
--   is added to the map.
countVarNamesWith :: ([IR.VarName] -> [IR.VarName] -> [IR.VarName])
                  -> (IR.VarName -> [IR.VarName] -> Bool)
                  -> [IR.VarName]
                  -> IR.Expr
                  -> Map IR.VarName Integer
countVarNamesWith _ f vns (IR.Var _ varName _)
  | varName `f` vns = Map.empty
  | otherwise = Map.singleton varName 1
countVarNamesWith g f vns (IR.App _ lhs rhs _)
  = countVarNamesWith g f vns lhs `mergeMap` countVarNamesWith g f vns rhs
countVarNamesWith g f vns (IR.TypeAppExpr _ lhs _ _)
  = countVarNamesWith g f vns lhs
countVarNamesWith g f vns (IR.If _ e1 e2 e3 _) = countVarNamesWith g f vns e1
  `mergeMap` countVarNamesWith g f vns e2
  `mergeMap` countVarNamesWith g f vns e3
countVarNamesWith _ _ _ IR.Con {} = Map.empty
countVarNamesWith _ _ _ IR.Undefined {} = Map.empty
countVarNamesWith _ _ _ IR.ErrorExpr {} = Map.empty
countVarNamesWith _ _ _ IR.IntLiteral {} = Map.empty
countVarNamesWith g f vns (IR.Case _ e alts _)
  = let altVars = concatMap (map IR.varPatQName . IR.altVarPats) alts
    in countVarNamesWith g f vns e
       `mergeMap` foldr
       (mergeMap . countVarNamesWith g f (g vns altVars) . IR.altRhs) Map.empty
       alts
countVarNamesWith g f vns (IR.Lambda _ exprArgs rhs _) = countVarNamesWith g f
  (g vns (map IR.varPatQName exprArgs)) rhs
countVarNamesWith g f vns (IR.Let _ binds e _)
  = let bindVars = map (IR.varPatQName . IR.bindVarPat) binds
    in countVarNamesWith g f (g vns bindVars) e
       `mergeMap` foldr
       (mergeMap . countVarNamesWith g f (g vns bindVars) . IR.bindExpr)
       Map.empty binds

mergeMap
  :: Map IR.VarName Integer -> Map IR.VarName Integer -> Map IR.VarName Integer
mergeMap = Map.unionWith (+)
