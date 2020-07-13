-- | This module contains functions for converting mutually recursive
--   function declarations by splitting them into one or more recursive helper
--   function, whose decreasing argument is not lifted to the @Free@ monad, and
--   a non-recursive main function.

module FreeC.Backend.Coq.Converter.FuncDecl.Rec.WithHelpers
  ( convertRecFuncDeclsWithHelpers
  , convertRecFuncDeclsWithHelpers'
  )
where

import           Control.Monad                  ( forM
                                                , mapAndUnzipM
                                                , join
                                                )
import           Data.List                      ( delete
                                                , elemIndex
                                                )
import qualified Data.List.NonEmpty            as NonEmpty
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( fromJust )
import qualified Data.Set                      as Set

import           FreeC.Backend.Coq.Analysis.DecreasingArguments
import           FreeC.Backend.Coq.Converter.Expr
import           FreeC.Backend.Coq.Converter.FuncDecl.Common
import           FreeC.Backend.Coq.Converter.FuncDecl.NonRec
import qualified FreeC.Backend.Coq.Syntax      as Coq
import           FreeC.Environment
import           FreeC.Environment.Entry
import           FreeC.Environment.Fresh
import           FreeC.Environment.Renamer
import           FreeC.IR.Inlining
import           FreeC.IR.Reference             ( freeVarSet )
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax               as IR
import           FreeC.IR.Subterm
import           FreeC.Monad.Converter
import           FreeC.Pretty
import           FreeC.Util.Predicate

-- | Converts recursive function declarations into recursive helper and
--   non-recursive main functions.
convertRecFuncDeclsWithHelpers :: [IR.FuncDecl] -> Converter [Coq.Sentence]
convertRecFuncDeclsWithHelpers decls = do
  (helperDecls', mainDecls') <- convertRecFuncDeclsWithHelpers' decls
  return
    (  Coq.comment
        ("Helper functions for " ++ showPretty (map IR.funcDeclName decls))
    :  helperDecls'
    ++ mainDecls'
    )

-- | Like 'convertRecFuncDeclsWithHelpers' but does return the helper and
--   main functions separately.
convertRecFuncDeclsWithHelpers'
  :: [IR.FuncDecl] -> Converter ([Coq.Sentence], [Coq.Sentence])
convertRecFuncDeclsWithHelpers' decls = do
  -- Split into helper and main functions.
  decArgs                  <- identifyDecArgs decls
  (helperDecls, mainDecls) <- mapAndUnzipM (uncurry transformRecFuncDecl)
                                           (zip decls decArgs)
  -- Convert helper and main functions.
  -- The right-hand sides of the main functions are inlined into the helper
  -- functions. Because inlining can produce fresh identifiers, we need to
  -- perform inlining and conversion of helper functions in a local environment.
  helperDecls' <- forM (concat helperDecls) $ \(helperDecl, decArgIndex) ->
    localEnv $ do
      inlinedHelperDecl <- inlineFuncDecls mainDecls helperDecl
      convertRecHelperFuncDecl inlinedHelperDecl decArgIndex
  mainDecls' <- convertNonRecFuncDecls mainDecls

  -- Create common fixpoint sentence for all helper functions.
  return
    ( [Coq.FixpointSentence (Coq.Fixpoint (NonEmpty.fromList helperDecls') [])]
    , mainDecls'
    )

-- | Transforms the given recursive function declaration with the specified
--   decreasing argument into recursive helper functions and a non recursive
--   main function.
--
--   The helper functions are annotated with the index of their decreasing
--   argument.
transformRecFuncDecl
  :: IR.FuncDecl
  -> DecArgIndex
  -> Converter ([(IR.FuncDecl, DecArgIndex)], IR.FuncDecl)
transformRecFuncDecl (IR.FuncDecl srcSpan declIdent typeArgs args maybeRetType expr) decArgIndex
  = do
  -- Generate a helper function declaration and application for each case
  -- expression of the decreasing argument.
    (helperDecls, helperApps) <- mapAndUnzipM generateHelperDecl caseExprsPos

    -- Generate main function declaration. The main function's right-hand side
    -- is constructed by replacing all @case@-expressions of the decreasing
    -- argument by an invocation of the corresponding recursive helper function.
    let mainExpr = replaceSubterms' expr (zip caseExprsPos helperApps)
        mainDecl =
          IR.FuncDecl srcSpan declIdent typeArgs args maybeRetType mainExpr

    return (helperDecls, mainDecl)
 where
  -- | The name of the function to transform.
  name :: IR.QName
  name = IR.declIdentName declIdent

  -- | The names of the function's arguments.
  argNames :: [IR.QName]
  argNames = map IR.varPatQName args

  -- | The name of the decreasing argument.
  decArg :: IR.QName
  decArg = argNames !! decArgIndex

  -- | The positions of @case@-expressions for the decreasing argument.
  caseExprsPos :: [Pos]
  caseExprsPos = [ p | p <- ps, not (any (below p) (delete p ps)) ]
   where
    ps :: [Pos]
    ps = filter decArgNotShadowed (findSubtermPos isCaseExpr expr)

  -- | Tests whether the given expression is a @case@-expression for the
  --   the decreasing argument.
  isCaseExpr :: IR.Expr -> Bool
  isCaseExpr (IR.Case _ (IR.Var _ varName _) _ _) = varName == decArg
  isCaseExpr _ = False

  -- | Ensures that the decreasing argument is not shadowed by the binding
  --   of a local variable at the given position.
  decArgNotShadowed :: Pos -> Bool
  decArgNotShadowed p = decArg `Set.notMember` boundVarsAt expr p

  -- | Generates the recursive helper function declaration for the @case@-
  --   expression at the given position of the right-hand side.
  --
  --   Returns the helper function declaration with the index of its decreasing
  --   argument and an expression for the application of the helper function.
  generateHelperDecl :: Pos -> Converter ((IR.FuncDecl, DecArgIndex), IR.Expr)
  generateHelperDecl caseExprPos = do
    -- Generate a fresh name for the helper function.
    helperName <- freshHaskellQName (IR.declIdentName declIdent)
    let helperDeclIdent = declIdent { IR.declIdentName = helperName }

    -- Pass all type arguments to the helper function.
    let helperTypeArgs  = typeArgs

    -- Pass used variables as additional arguments to the helper function
    -- but don't pass shadowed arguments to helper functions.
    let boundVarTypeMap = boundVarsWithTypeAt expr caseExprPos
        boundVars =
          Map.keysSet boundVarTypeMap `Set.union` Set.fromList argNames
        caseExpr       = selectSubterm' expr caseExprPos
        usedVars       = freeVarSet caseExpr
        helperArgNames = Set.toList (usedVars `Set.intersection` boundVars)

    -- Determine the types of helper function's arguments and its return type.
    -- Additionally, the decreasing argument is marked as strict.
    let
      argTypes         = map IR.varPatType args
      argTypeMap       = Map.fromList (zip argNames argTypes)
      helperArgTypeMap = boundVarTypeMap `Map.union` argTypeMap
      helperArgTypes =
        map (join . (`Map.lookup` helperArgTypeMap)) helperArgNames
      argStrict       = map IR.varPatIsStrict args
      argStrictMap    = Map.fromList (zip argNames argStrict)
      helperArgStrict = map
        ((== decArg) .||. ((Just True ==) . (`Map.lookup` argStrictMap)))
        helperArgNames
      helperArgs = zipWith3
        (IR.VarPat NoSrcSpan . fromJust . IR.identFromQName)
        helperArgNames
        helperArgTypes
        helperArgStrict
      helperReturnType = IR.exprType caseExpr
      helperType =
        IR.funcType NoSrcSpan <$> sequence helperArgTypes <*> helperReturnType

    -- Register the helper function to the environment.
    -- Even though we know the type of the original and additional arguments
    -- the return type is unknown, since the right-hand side of @case@
    -- expressions is not annotated.
    -- If the original function was partial, the helper function is partial as
    -- well.
    freeArgsNeeded <- inEnv $ needsFreeArgs name
    partial        <- inEnv $ isPartial name
    _entry         <- renameAndAddEntry $ FuncEntry
      { entrySrcSpan       = NoSrcSpan
      , entryArity         = length helperArgTypes
      , entryTypeArgs      = map IR.typeVarDeclIdent helperTypeArgs
      , entryArgTypes      = map fromJust helperArgTypes
      , entryStrictArgs    = map IR.varPatIsStrict helperArgs
      , entryReturnType    = fromJust helperReturnType
      , entryNeedsFreeArgs = freeArgsNeeded
      , entryIsPartial     = partial
      , entryName          = helperName
      , entryIdent         = undefined -- filled by renamer
      , entryAgdaIdent     = undefined -- filled by renamer
      }

    -- Determine the index of the decreasing argument.
    let decArgIndex' = fromJust $ elemIndex decArg helperArgNames

    -- Build helper function declaration and application.
    let helperTypeArgs' = map IR.typeVarDeclToType helperTypeArgs
        helperAppType   = IR.TypeSchema NoSrcSpan [] <$> helperType
        helperDecl      = IR.FuncDecl srcSpan
                                      helperDeclIdent
                                      helperTypeArgs
                                      helperArgs
                                      helperReturnType
                                      caseExpr
        helperApp = IR.app
          NoSrcSpan
          (IR.visibleTypeApp NoSrcSpan
                             (IR.Var NoSrcSpan helperName helperAppType)
                             helperTypeArgs'
          )
          (map IR.varPatToExpr helperArgs)

    return ((helperDecl, decArgIndex'), helperApp)

-- | Converts a recursive helper function to the body of a Coq @Fixpoint@
--   sentence with the decreasing argument at the given index annotated with
--   @struct@.
convertRecHelperFuncDecl :: IR.FuncDecl -> DecArgIndex -> Converter Coq.FixBody
convertRecHelperFuncDecl helperDecl decArgIndex = localEnv $ do
  -- Convert left- and right-hand side of helper function.
  (qualid, binders, returnType') <- convertFuncHead helperDecl
  rhs'                           <- convertExpr (IR.funcDeclRhs helperDecl)
  -- Lookup name of decreasing argument.
  Just decArg'                   <-
    inEnv
    $  lookupIdent IR.ValueScope
    $  IR.varPatQName
    $  IR.funcDeclArgs helperDecl
    !! decArgIndex
  -- Generate body of @Fixpoint@ sentence.
  return
    (Coq.FixBody qualid
                 (NonEmpty.fromList binders)
                 (Just (Coq.StructOrder decArg'))
                 returnType'
                 rhs'
    )
