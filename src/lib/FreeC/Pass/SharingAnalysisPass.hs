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
module FreeC.Pass.SharingAnalysisPass
  ( sharingAnaylsisPass
  , analyseSharingExpr
  , analyseLocalSharing
  ) where

import           Control.Monad           ( (>=>), foldM, mapAndUnzipM )
import           Data.Map.Strict         ( Map )
import qualified Data.Map.Strict         as Map
import           Data.Set                as Set ( fromList )

import           FreeC.Environment       ( lookupEntry )
import           FreeC.Environment.Entry
import           FreeC.Environment.Fresh ( freshHaskellName )
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
analyseSharingDecl funcDecl = do
  let declArgs = IR.funcDeclArgs funcDecl
  rhs' <- ((analyseLocalSharing declArgs) >=> analyseSharingExpr declArgs)
    (IR.funcDeclRhs funcDecl)
  return funcDecl { IR.funcDeclRhs = rhs' }

-- | Checks the expression and all right-hand sides of subexpressions
--   for shared variables that are introduced through @case@-alternatives
--   or lambda abstractions.
--
--   If a variable is shared, a @let@-expression that makes the sharing
--   explicit is introduced.
analyseLocalSharing :: [IR.VarPat] -> IR.Expr -> Converter IR.Expr
analyseLocalSharing varPats (IR.Case srcSpan expr alts typeScheme) = do
  expr' <- analyseLocalSharing varPats expr
  alts' <- mapM analyseSharingAlt alts
  return (IR.Case srcSpan expr' alts' typeScheme)
 where
  analyseSharingAlt :: IR.Alt -> Converter IR.Alt
  analyseSharingAlt (IR.Alt altSrcSpan altConPat altVarPats altRhs) = do
    let varPats' = varPats ++ altVarPats
    altRhs'
      <- analyseLocalSharing varPats' altRhs >>= analyseSharingExpr varPats'
    return (IR.Alt altSrcSpan altConPat altVarPats altRhs')
analyseLocalSharing varPats (IR.Lambda srcSpan exprArgs rhs typeScheme) = do
  let varPats' = varPats ++ exprArgs
  rhs' <- (analyseLocalSharing varPats' >=> analyseSharingExpr varPats') rhs
  return (IR.Lambda srcSpan exprArgs rhs' typeScheme)
analyseLocalSharing _ expr@IR.Con {} = return expr
analyseLocalSharing _ expr@IR.Undefined {} = return expr
analyseLocalSharing _ expr@IR.ErrorExpr {} = return expr
analyseLocalSharing _ expr@IR.Var {} = return expr
analyseLocalSharing _ expr@IR.IntLiteral {} = return expr
analyseLocalSharing varPats (IR.Let srcSpan binds rhs typeScheme) = do
  binds' <- mapM analyseSharingBind binds
  rhs' <- analyseLocalSharing varPats rhs
  return (IR.Let srcSpan binds' rhs' typeScheme)
 where
  analyseSharingBind :: IR.Bind -> Converter IR.Bind
  analyseSharingBind (IR.Bind bindSrcSpan bindVarPat bindRhs) = do
    bindRhs' <- analyseLocalSharing varPats bindRhs
    return (IR.Bind bindSrcSpan bindVarPat bindRhs')
analyseLocalSharing varPats (IR.If srcSpan e1 e2 e3 typeScheme) = do
  e1' <- analyseLocalSharing varPats e1
  e2' <- analyseLocalSharing varPats e2
  e3' <- analyseLocalSharing varPats e3
  return (IR.If srcSpan e1' e2' e3' typeScheme)
analyseLocalSharing varPats (IR.TypeAppExpr srcSpan lhs rhs typeScheme) = do
  lhs' <- analyseLocalSharing varPats lhs
  return (IR.TypeAppExpr srcSpan lhs' rhs typeScheme)
analyseLocalSharing varPats expr@(IR.App srcSpan lhs rhs typeScheme) = do
  encSharing <- shouldEncapsulateSharing lhs
  if encSharing then encapsulateSharing varPats expr else do
    lhs' <- analyseLocalSharing varPats lhs
    rhs' <- analyseLocalSharing varPats rhs
    return (IR.App srcSpan lhs' rhs' typeScheme)

-- | Returns the function or constructor name of an application.
getLeftmostSymbol :: IR.Expr -> IR.VarName
getLeftmostSymbol (IR.Var _ varName _) = varName
getLeftmostSymbol (IR.App _ lhs _ _)   = getLeftmostSymbol lhs
getLeftmostSymbol _
  = error "getLeftmostSymbol: unexpected expression"

-- | Whether an expression is an application of a function that encapsulates
--   effects.
shouldEncapsulateSharing :: IR.Expr -> Converter Bool
shouldEncapsulateSharing expr = do
  let funcName = getLeftmostSymbol expr
  Just entry <- inEnv $ lookupEntry IR.ValueScope funcName
  if isFuncEntry entry
    then return $ entryEncapsulatesEffects entry
    else return False

-- | Builds let expressions for variables with more than one occurrence
--   for each argument of a function that encapsulates effects.
encapsulateSharing :: [IR.VarPat] -> IR.Expr -> Converter IR.Expr
encapsulateSharing _ var@(IR.Var _ _ _) = return var
encapsulateSharing varPats (IR.App srcSpan lhs rhs typeScheme) = do
  rhs' <- analyseLocalSharing varPats rhs >>= analyseSharingExpr varPats
  lhs' <- encapsulateSharing varPats lhs
  return (IR.App srcSpan lhs' rhs' typeScheme)
encapsulateSharing _ _ = error "encapsulateSharing: unexpected expression"

-- | Checks if an expression contains variables that occur
--   multiple times on the same right-hand side.
--   If that is the case, a @let@-expression is introduced that binds the
--   variables to fresh ones and replaces the occurrences with the newly
--   introduced variable.
analyseSharingExpr :: [IR.VarPat] -> IR.Expr -> Converter IR.Expr
analyseSharingExpr varPats expr = do
  let varPatNames = map IR.varPatQName varPats
  varMap <- countVarNamesOnly varPatNames expr
  let varList = (map fst . filter ((> 1) . snd) . Map.toList) varMap
  buildLet expr varList

-- | Builds a @let@-expression from the given expression and variable names.
--
--   Computes @let@-bindings from the given variables, composes the resulting
--   substitutions and applies the substitution on the expression.
buildLet :: IR.Expr -> [IR.VarName] -> Converter IR.Expr
buildLet expr []   = return expr
buildLet expr vars = localEnv $ do
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
    varName' <- freshHaskellName (IR.nameFromQName varName)
    let subst            = singleSubst' varName
          (\s -> IR.Var s (IR.UnQual varName') Nothing)
        rhs              = IR.Var srcSpan varName Nothing
        Just varPatIdent = IR.identFromName varName'
        varPat           = IR.VarPat srcSpan varPatIdent Nothing False
        bind             = IR.Bind srcSpan varPat rhs
    return (bind, subst)

-- | Counts all variable names on right-hand sides of expression that are also
--   contained by the given list.
--   Shadowed variables and variables from the list are not counted.
--   Variables introduced on the left side of a @case@-alternative and @let@
--   expressions are not counted as well.
countVarNamesOnly
  :: [IR.VarName] -> IR.Expr -> Converter (Map IR.VarName Integer)
countVarNamesOnly varNames expr = do
  varMap <- countVarNames expr
  return $ varMap `Map.restrictKeys` Set.fromList varNames

-- | Counts all variable names on right-hand sides of expression.
--   Shadowed variables and variables from the list are not counted.
--   Variables introduced on the left side of a @case@-alternative and @let@
--   expressions are not counted as well.
countVarNames :: IR.Expr -> Converter (Map IR.VarName Integer)
countVarNames (IR.Var _ varName _)       = return $ Map.singleton varName 1
countVarNames (IR.App _ lhs rhs _)       = do
  encSharing <- shouldEncapsulateSharing lhs
  -- Do not count variables that occur in applications of functions that
  -- encapsulate effects.
  if encSharing then return Map.empty else do
    lhsVars <- countVarNames lhs
    rhsVars <- countVarNames rhs
    return $ lhsVars `mergeMap` rhsVars
countVarNames (IR.TypeAppExpr _ lhs _ _) = countVarNames lhs
countVarNames (IR.If _ e1 e2 e3 _)       = do
  map1 <- countVarNames e1
  map2 <- countVarNames e2
  map3 <- countVarNames e3
  return $ map1 `mergeMap` Map.unionWith max map2 map3
countVarNames IR.Con {}                  = return $ Map.empty
countVarNames IR.Undefined {}            = return $ Map.empty
countVarNames IR.ErrorExpr {}            = return $ Map.empty
countVarNames IR.IntLiteral {}           = return $ Map.empty
countVarNames (IR.Case _ e alts _)       = do
  let altVars = concatMap (map IR.varPatQName . IR.altVarPats) alts
  map1 <- countVarNames e
  map2 <- foldM (\m alt -> mergeMap m <$> countVarNames (IR.altRhs alt))
    Map.empty alts
  map3 <- foldM (\m alt -> Map.unionWith max m
                 <$> countVarNames (IR.altRhs alt)) Map.empty alts
  let completeMap = map1 `mergeMap` map2 `mergeMap` map3
  return $ completeMap `Map.withoutKeys` Set.fromList altVars
countVarNames (IR.Lambda _ args rhs _)   = do
  rhsVars <- countVarNames rhs
  return $ rhsVars `Map.withoutKeys` Set.fromList (map IR.varPatQName args)
countVarNames (IR.Let _ binds e _)       = do
  let bindVars = map (IR.varPatQName . IR.bindVarPat) binds
  map1 <- countVarNames e
  map2 <- foldM (\m bind -> mergeMap m <$> countVarNames (IR.bindExpr bind))
    Map.empty binds
  let completeMap = mergeMap map1 map2
   {- completeMap = countVarNames e
          `mergeMap` foldr (mergeMap . countVarNames . IR.bindExpr) Map.empty
          binds-}
  return $ completeMap `Map.withoutKeys` Set.fromList bindVars

mergeMap
  :: Map IR.VarName Integer -> Map IR.VarName Integer -> Map IR.VarName Integer
mergeMap = Map.unionWith (+)
