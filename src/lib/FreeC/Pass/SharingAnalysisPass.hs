module FreeC.Pass.SharingAnalysisPass ( sharingAnaylsisPass ) where

import FreeC.Environment.Fresh ( freshHaskellQName )
import qualified FreeC.IR.Syntax as IR
import FreeC.IR.Subst
import FreeC.IR.SrcSpan
import FreeC.Monad.Converter
import FreeC.Pass
import Control.Monad ( foldM, mplus )
import Data.Map.Strict ( Map )
import qualified Data.Map.Strict as Map
import Data.Maybe ( fromJust )

sharingAnaylsisPass :: Pass IR.Module
sharingAnaylsisPass
    (IR.Module srcSpan name imports typeDecls typeSigs pragmas funcDecls) = do
        funcDecls' <- mapM analyseSharingDecl (funcDecls)
        return (IR.Module srcSpan name imports typeDecls typeSigs pragmas
                funcDecls')

analyseSharingDecl :: IR.FuncDecl -> Converter IR.FuncDecl
analyseSharingDecl (IR.FuncDecl srcSpan ident typeArgs args returnType rhs) = do
    let varList = (map (\p -> ( fst p, snd $ snd p )) . filter
                   ((> 1) . fst . snd) . Map.toList . countVarNames) rhs
    rhs' <- buildLet rhs varList
    return (IR.FuncDecl srcSpan ident typeArgs args returnType rhs')

buildLet
    :: IR.Expr -> [ ( IR.VarName, Maybe IR.TypeScheme ) ] -> Converter IR.Expr
buildLet expr vars = do
    let srcSpan = IR.exprSrcSpan expr
    ( binds, substs ) <- buildBinds srcSpan vars
    return (IR.Let srcSpan binds (applySubst (composeSubsts substs) expr)
            (IR.exprTypeScheme expr))

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
            rhs = IR.Var srcSpan varName' varTypeScheme -- This type scheme has wrong srcSpanInformation
            varPat = IR.VarPat srcSpan (fromJust (IR.identFromQName varName'))
                (fmap IR.typeSchemeType varTypeScheme) False
            bind = IR.Bind srcSpan varPat rhs
        return ( bind : binds, subst : substs )

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
