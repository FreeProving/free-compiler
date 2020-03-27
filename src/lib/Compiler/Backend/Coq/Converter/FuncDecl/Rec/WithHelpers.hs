-- | This module contains functions for converting mutually recursive
--   function declarations by spliting when into one or more recursive helper
--   function whose decreasing argument is not lifted to the @Free@ monad and
--   a non-recursive main function.

module Compiler.Backend.Coq.Converter.FuncDecl.Rec.WithHelpers
  ( convertRecFuncDeclsWithHelpers
  , convertRecFuncDeclsWithHelpers'
  )
where

import           Control.Monad                  ( mapAndUnzipM
                                                , join
                                                )
import           Data.List                      ( delete
                                                , elemIndex
                                                )
import qualified Data.List.NonEmpty            as NonEmpty
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( fromJust )
import qualified Data.Set                      as Set

import           Compiler.Analysis.RecursionAnalysis
import           Compiler.Backend.Coq.Converter.Expr
import           Compiler.Backend.Coq.Converter.FuncDecl.Common
import           Compiler.Backend.Coq.Converter.FuncDecl.NonRec
import qualified Compiler.Backend.Coq.Syntax   as G
import           Compiler.Environment
import           Compiler.Environment.Entry
import           Compiler.Environment.Fresh
import           Compiler.Environment.Renamer
import           Compiler.Environment.Scope
import           Compiler.IR.Inlining
import           Compiler.IR.Reference          ( freeVarSet )
import           Compiler.IR.SrcSpan
import qualified Compiler.IR.Syntax            as HS
import           Compiler.IR.Subterm
import           Compiler.Monad.Converter
import           Compiler.Pretty

-- | Converts recursive function declarations into recursive helper and
--   non-recursive main functions.
convertRecFuncDeclsWithHelpers :: [HS.FuncDecl] -> Converter [G.Sentence]
convertRecFuncDeclsWithHelpers decls = do
  (helperDecls', mainDecls') <- convertRecFuncDeclsWithHelpers' decls
  return
    (  G.comment
        ("Helper functions for " ++ showPretty (map HS.funcDeclName decls))
    :  helperDecls'
    ++ mainDecls'
    )

-- | Like 'convertRecFuncDeclsWithHelpers' but does return the helper and
--   main functions separtly.
convertRecFuncDeclsWithHelpers'
  :: [HS.FuncDecl] -> Converter ([G.Sentence], [G.Sentence])
convertRecFuncDeclsWithHelpers' decls = do
  -- Split into helper and main functions.
  decArgs                  <- identifyDecArgs decls
  (helperDecls, mainDecls) <- mapAndUnzipM (uncurry transformRecFuncDecl)
                                           (zip decls decArgs)
  -- Convert helper and main functions.
  -- The right hand side of the main functions are inlined into helper the
  -- functions. Because inlining can produce fesh identifiers, we need to
  -- perform inlining and conversion of helper functions in a local environment.
  helperDecls' <- flip mapM (concat helperDecls) $ \helperDecl -> localEnv $ do
    inlinedHelperDecl <- inlineFuncDecls mainDecls helperDecl
    convertRecHelperFuncDecl inlinedHelperDecl
  mainDecls' <- mapM convertNonRecFuncDecl mainDecls

  -- Create common fixpoint sentence for all helper functions.
  return
    ( [G.FixpointSentence (G.Fixpoint (NonEmpty.fromList helperDecls') [])]
    , mainDecls'
    )

-- | Transforms the given recursive function declaration with the specified
--   decreasing argument into recursive helper functions and a non recursive
--   main function.
transformRecFuncDecl
  :: HS.FuncDecl -> DecArgIndex -> Converter ([HS.FuncDecl], HS.FuncDecl)
transformRecFuncDecl (HS.FuncDecl srcSpan declIdent typeArgs args expr maybeRetType) decArgIndex
  = do
  -- Generate a helper function declaration and application for each case
  -- expression of the decreasing argument.
    (helperDecls, helperApps) <- mapAndUnzipM generateHelperDecl caseExprsPos

    -- Generate main function declaration. The main function's right hand side
    -- is constructed by replacing all case expressions of the decreasing
    -- argument by an invocation of the corresponding recursive helper function.
    let (Just mainExpr) = replaceSubterms expr (zip caseExprsPos helperApps)
        mainDecl =
          HS.FuncDecl srcSpan declIdent typeArgs args mainExpr maybeRetType

    -- If the user specified the decreasing argument of the function to
    -- transform, that information needs to be removed since the main function
    -- is not recursive anymore.
    modifyEnv $ removeDecArg name

    return (helperDecls, mainDecl)
 where
  -- | The name of the function to transform.
  name :: HS.QName
  name = HS.declIdentName declIdent

  -- | The names of the function's arguments.
  argNames :: [HS.QName]
  argNames = map HS.varPatQName args

  -- | The name of the decreasing argument.
  decArg :: HS.QName
  decArg = argNames !! decArgIndex

  -- | The positions of @case@-expressions for the decreasing argument.
  caseExprsPos :: [Pos]
  caseExprsPos = [ p | p <- ps, all (not . below p) (delete p ps) ]
   where
    ps :: [Pos]
    ps = filter decArgNotShadowed (findSubtermPos isCaseExpr expr)

  -- | Tests whether the given expression is a @case@-expression for the
  --   the decreasing argument.
  isCaseExpr :: HS.Expr -> Bool
  isCaseExpr (HS.Case _ (HS.Var _ varName _) _ _) = varName == decArg
  isCaseExpr _ = False

  -- | Ensures that the decreasing argument is not shadowed by the binding
  --   of a local variable at the given position.
  decArgNotShadowed :: Pos -> Bool
  decArgNotShadowed p = decArg `Set.notMember` boundVarsAt expr p

  -- | Generates the recursive helper function declaration for the @case@
  --   expression at the given position of the right hand side.
  --
  --   Returns the helper function declaration and an expression for the
  --   application of the helper function.
  generateHelperDecl :: Pos -> Converter (HS.FuncDecl, HS.Expr)
  generateHelperDecl caseExprPos = do
    -- Generate a fresh name for the helper function.
    helperName <- freshHaskellQName (HS.declIdentName declIdent)
    let helperDeclIdent = declIdent { HS.declIdentName = helperName }

    -- Pass all type arguments to the helper function.
    let helperTypeArgs  = typeArgs

    -- Pass used variables as additional arguments to the helper function
    -- but don't pass shadowed arguments to helper functions.
    let boundVarTypeMap = boundVarsWithTypeAt expr caseExprPos
        boundVars =
          Map.keysSet boundVarTypeMap `Set.union` Set.fromList argNames
        Just caseExpr  = selectSubterm expr caseExprPos
        usedVars       = freeVarSet caseExpr
        helperArgNames = Set.toList (usedVars `Set.intersection` boundVars)

    -- Determine the type of helper function's arguments and its return type.
    let
      argTypes         = map HS.varPatType args
      argTypeMap       = Map.fromList (zip argNames argTypes)
      helperArgTypeMap = boundVarTypeMap `Map.union` argTypeMap
      helperArgTypes =
        map (join . (`Map.lookup` helperArgTypeMap)) helperArgNames
      helperArgs = zipWith
        (HS.VarPat NoSrcSpan . fromJust . HS.identFromQName)
        helperArgNames
        helperArgTypes
      helperReturnType = HS.exprType caseExpr
      helperType       = do
        helperArgTypes'   <- sequence helperArgTypes
        helperReturnType' <- helperReturnType
        return (HS.funcType NoSrcSpan helperArgTypes' helperReturnType')

    -- Register the helper function to the environment.
    -- Even though we know the type of the original and additional arguments
    -- the return type is unknown since @case@ the right-hand side of @case@
    -- expressions is not annotated.
    -- If the original function was partial, the helper function is partial as
    -- well.
    freeArgsNeeded <- inEnv $ needsFreeArgs name
    partial        <- inEnv $ isPartial name
    _              <- renameAndAddEntry $ FuncEntry
      { entrySrcSpan       = NoSrcSpan
      , entryArity         = length helperArgTypes
      , entryTypeArgs      = map HS.typeVarDeclIdent helperTypeArgs
      , entryArgTypes      = helperArgTypes
      , entryReturnType    = helperReturnType
      , entryNeedsFreeArgs = freeArgsNeeded
      , entryIsPartial     = partial
      , entryName          = helperName
      , entryIdent         = undefined -- filled by renamer
      }

    -- Additionally we need to remember the index of the decreasing argument
    -- (see 'convertArgs').
    let Just decArgIndex' = elemIndex decArg helperArgNames
        Just decArgIdent  = HS.identFromQName decArg
    modifyEnv $ defineDecArg helperName decArgIndex' decArgIdent

    -- Build helper function declaration and application.
    let helperTypeArgs' = map HS.typeVarDeclToType helperTypeArgs
        helperAppType   = HS.TypeSchema NoSrcSpan [] <$> helperType
        helperDecl      = HS.FuncDecl srcSpan
                                      helperDeclIdent
                                      helperTypeArgs
                                      helperArgs
                                      caseExpr
                                      helperReturnType
        helperApp = HS.app
          NoSrcSpan
          (HS.visibleTypeApp NoSrcSpan
                             (HS.Var NoSrcSpan helperName helperAppType)
                             helperTypeArgs'
          )
          (map (HS.varPatToExpr) helperArgs)

    return (helperDecl, helperApp)

-- | Converts a recursive helper function to the body of a Coq @Fixpoint@
--   sentence.
convertRecHelperFuncDecl :: HS.FuncDecl -> Converter G.FixBody
convertRecHelperFuncDecl helperDecl = localEnv $ do
  -- Convert left- and right-hand side of helper function.
  (qualid, binders, returnType') <- convertFuncHead helperDecl
  rhs'                           <- convertExpr (HS.funcDeclRhs helperDecl)
  -- Lookup name of decreasing argument.
  let helperName = HS.funcDeclQName helperDecl
      argNames   = map HS.varPatQName (HS.funcDeclArgs helperDecl)
  Just decArgIndex <- inEnv $ lookupDecArgIndex helperName
  Just decArg'     <- inEnv $ lookupIdent ValueScope (argNames !! decArgIndex)
  -- Generate body of @Fixpoint@ sentence.
  return
    (G.FixBody qualid
               (NonEmpty.fromList binders)
               (Just (G.StructOrder decArg'))
               returnType'
               rhs'
    )
