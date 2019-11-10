-- | This module contains functions for converting function declarations from
--   Haskell to Coq.

module Compiler.Converter.FuncDecl where

import           Control.Monad                  ( mapAndUnzipM )
import qualified Data.List.NonEmpty            as NonEmpty
import           Data.Maybe                     ( catMaybes
                                                , fromJust
                                                )
import qualified Data.Set                      as Set

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Analysis.DependencyExtraction
                                                ( typeVars )
import           Compiler.Analysis.PartialityAnalysis
import           Compiler.Analysis.RecursionAnalysis
import           Compiler.Converter.Arg
import           Compiler.Converter.Expr
import           Compiler.Converter.Free
import           Compiler.Converter.Type
import qualified Compiler.Coq.AST              as G
import           Compiler.Environment
import           Compiler.Environment.Entry
import           Compiler.Environment.Fresh
import           Compiler.Environment.LookupOrFail
import           Compiler.Environment.Renamer
import           Compiler.Environment.Scope
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.Inliner
import           Compiler.Haskell.SrcSpan
import           Compiler.Haskell.Subterm
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty

-------------------------------------------------------------------------------
-- Strongly connected components                                             --
-------------------------------------------------------------------------------

-- | Converts a strongly connected component of the function dependency graph.
convertFuncComponent
  :: DependencyComponent HS.FuncDecl -> Converter [G.Sentence]
convertFuncComponent (NonRecursive decl) = do
  defineFuncDecl decl
  decl' <- convertNonRecFuncDecl decl
  return [decl']
convertFuncComponent (Recursive decls) = do
  mapM_ defineFuncDecl decls
  convertRecFuncDecls decls

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

-- | Converts the name, arguments and return type of a function to Coq.
--
--   This code is shared between the conversion functions for recursive and
--   no recursive functions (see 'convertNonRecFuncDecl' and
--   'convertRecFuncDecls').
convertFuncHead
  :: HS.QName    -- ^ The name of the function.
  -> [HS.VarPat] -- ^ The function argument patterns.
  -> Converter (G.Qualid, [G.Binder], Maybe G.Term)
convertFuncHead name args = do
  -- Lookup the Coq name of the function.
  Just qualid       <- inEnv $ lookupIdent ValueScope name
    -- Lookup type signature and partiality.
  partial           <- inEnv $ isPartial name
  Just usedTypeVars <- inEnv $ lookupTypeArgs ValueScope name
  Just argTypes     <- inEnv $ lookupArgTypes ValueScope name
  returnType        <- inEnv $ lookupReturnType ValueScope name
  -- Convert arguments and return type.
  typeVarDecls'     <- generateTypeVarDecls G.Implicit usedTypeVars
  decArgIndex       <- inEnv $ lookupDecArg name
  args'             <- convertArgs args argTypes decArgIndex
  returnType'       <- mapM convertType returnType
  return
    ( qualid
    , (  genericArgDecls G.Explicit
      ++ [ partialArgDecl | partial ]
      ++ typeVarDecls'
      ++ args'
      )
    , returnType'
    )

-- | Inserts the given function declaration into the current environment.
defineFuncDecl :: HS.FuncDecl -> Converter ()
defineFuncDecl decl@(HS.FuncDecl srcSpan (HS.DeclIdent _ ident) args _) = do
  let name = HS.UnQual (HS.Ident ident)
  funcType               <- lookupTypeSigOrFail srcSpan name
  (argTypes, returnType) <- splitFuncType name args funcType
  partial                <- isPartialFuncDecl decl
  _                      <- renameAndAddEntry FuncEntry
    { entrySrcSpan    = srcSpan
    , entryArity      = length argTypes
    , entryTypeArgs   = catMaybes $ map HS.identFromQName $ typeVars funcType
    , entryArgTypes   = map Just argTypes
    , entryReturnType = Just returnType
    , entryIsPartial  = partial
    , entryName       = HS.UnQual (HS.Ident ident)
    , entryIdent      = undefined -- filled by renamer
    }
  return ()

-- | Splits the annotated type of a Haskell function with the given arguments
--   into its argument and return types.
--
--   Type synonyms are expanded if neccessary.
splitFuncType
  :: HS.QName    -- ^ The name of the function to display in error messages.
  -> [HS.VarPat] -- ^ The argument variable patterns whose types to split of.
  -> HS.Type     -- ^ The type to split.
  -> Converter ([HS.Type], HS.Type)
splitFuncType name = splitFuncType'
 where
  splitFuncType' :: [HS.VarPat] -> HS.Type -> Converter ([HS.Type], HS.Type)
  splitFuncType' []         typeExpr              = return ([], typeExpr)
  splitFuncType' (_ : args) (HS.TypeFunc _ t1 t2) = do
    (argTypes, returnType) <- splitFuncType' args t2
    return (t1 : argTypes, returnType)
  splitFuncType' args@(arg : _) typeExpr = do
    typeExpr' <- expandTypeSynonym typeExpr
    if typeExpr /= typeExpr'
      then splitFuncType' args typeExpr'
      else
        reportFatal
        $  Message (HS.getSrcSpan arg) Error
        $  "Could not determine type of argument '"
        ++ HS.fromVarPat arg
        ++ "' for function '"
        ++ showPretty name
        ++ "'."

-------------------------------------------------------------------------------
-- Non-recursive function declarations                                       --
-------------------------------------------------------------------------------

-- | Converts a non-recursive Haskell function declaration to a Coq
--   @Definition@ sentence.
convertNonRecFuncDecl :: HS.FuncDecl -> Converter G.Sentence
convertNonRecFuncDecl (HS.FuncDecl _ (HS.DeclIdent _ ident) args expr) =
  localEnv $ do
    let name = HS.UnQual (HS.Ident ident)
    (qualid, binders, returnType') <- convertFuncHead name args
    expr'                          <- convertExpr expr
    return (G.definitionSentence qualid binders returnType' expr')

-------------------------------------------------------------------------------
-- Recursive function declarations                                           --
-------------------------------------------------------------------------------

-- | Converts (mutually) recursive Haskell function declarations to Coq.
convertRecFuncDecls :: [HS.FuncDecl] -> Converter [G.Sentence]
convertRecFuncDecls decls = do
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
    ( G.comment ("Helper functions for " ++ HS.prettyDeclIdents decls)
    : G.FixpointSentence (G.Fixpoint (NonEmpty.fromList helperDecls') [])
    : mainDecls'
    )

-- | Transforms the given recursive function declaration with the specified
--   decreasing argument into recursive helper functions and a non recursive
--   main function.
transformRecFuncDecl
  :: HS.FuncDecl -> DecArgIndex -> Converter ([HS.FuncDecl], HS.FuncDecl)
transformRecFuncDecl (HS.FuncDecl srcSpan declIdent args expr) decArgIndex = do
  -- Generate a helper function declaration and application for each case
  -- expression of the decreasing argument.
  (helperDecls, helperApps) <- mapAndUnzipM generateHelperDecl caseExprsPos

  -- Generate main function declaration. The main function's right hand side
  -- is constructed by replacing all case expressions of the decreasing
  -- argument by an invocation of the corresponding recursive helper function.
  let (Just mainExpr) = replaceSubterms expr (zip caseExprsPos helperApps)
      mainDecl        = HS.FuncDecl srcSpan declIdent args mainExpr

  return (helperDecls, mainDecl)
 where
  -- | The name of the function to transform.
  name :: HS.QName
  name = HS.UnQual (HS.Ident (HS.fromDeclIdent declIdent))

  -- | The names of the function's arguments.
  argNames :: [HS.QName]
  argNames = map (HS.UnQual . HS.Ident . HS.fromVarPat) args

  -- | The name of the decreasing argument.
  decArg :: HS.QName
  decArg = argNames !! decArgIndex

  -- | The positions of @case@-expressions for the decreasing argument.
  --
  --   TODO restrict to outermost positions.
  caseExprsPos :: [Pos]
  caseExprsPos = filter decArgNotShadowed (findSubtermPos isCaseExpr expr)

  -- | Tests whether the given expression is a @case@-expression for the
  --   the decreasing argument.
  isCaseExpr :: HS.Expr -> Bool
  isCaseExpr (HS.Case _ (HS.Var _ varName) _) = varName == decArg
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
  --
  --   TODO the original function arguments could be shadowed in the case
  --        expression. We must not pass those arguments to the helper
  --        function (if the arguments that shadow the original arguments
  --        are used, they are passed as additional arguments).
  generateHelperDecl :: Pos -> Converter (HS.FuncDecl, HS.Expr)
  generateHelperDecl caseExprPos = do
    -- Generate a fresh name for the helper function.
    helperIdent <- freshHaskellIdent (HS.fromDeclIdent declIdent)
    let helperName      = HS.UnQual (HS.Ident helperIdent)
        helperDeclIdent = HS.DeclIdent (HS.getSrcSpan declIdent) helperIdent

    -- Pass used variables as additional arguments to the helper function.
    let usedVars = Set.toList (usedVarsAt expr caseExprPos)
        helperArgs =
          args
            ++ map (HS.VarPat NoSrcSpan . fromJust . HS.identFromQName) usedVars

    -- Build helper function declaration and application.
    let (Just caseExpr) = selectSubterm expr caseExprPos
        helperDecl = HS.FuncDecl srcSpan helperDeclIdent helperArgs caseExpr
        helperApp = HS.app NoSrcSpan
                           (HS.Var NoSrcSpan helperName)
                           (map (HS.Var NoSrcSpan) (argNames ++ usedVars))

    -- Register the helper function to the environment.
    -- The types of the original parameters are known, but we neither know the
    -- type of the additional parameters nor the return type of the helper
    -- function.
    -- If the original function was partial, the helper function is partial as
    -- well.
    funcType      <- lookupTypeSigOrFail srcSpan name
    (argTypes, _) <- splitFuncType name args funcType
    let argTypes' = map Just argTypes ++ replicate (length usedVars) Nothing
    partial <- inEnv $ isPartial name
    _       <- renameAndAddEntry $ FuncEntry
      { entrySrcSpan    = NoSrcSpan
      , entryArity      = length argTypes'
      , entryTypeArgs   = catMaybes $ map HS.identFromQName $ typeVars funcType
      , entryArgTypes   = argTypes'
      , entryReturnType = Nothing
      , entryIsPartial  = partial
      , entryName       = HS.UnQual (HS.Ident helperIdent)
      , entryIdent      = undefined -- filled by renamer
      }

    -- Additionally we need to remember the index of the decreasing argument
    -- (see 'convertDecArg').
    modifyEnv $ defineDecArg helperName decArgIndex

    return (helperDecl, helperApp)

-- | Converts a recursive helper function to the body of a Coq @Fixpoint@
--   sentence.
convertRecHelperFuncDecl :: HS.FuncDecl -> Converter G.FixBody
convertRecHelperFuncDecl (HS.FuncDecl _ declIdent args expr) = localEnv $ do
  let helperName = HS.UnQual (HS.Ident (HS.fromDeclIdent declIdent))
      argNames   = map (HS.UnQual . HS.Ident . HS.fromVarPat) args
  (qualid, binders, returnType') <- convertFuncHead helperName args
  expr'                          <- convertExpr expr
  Just decArgIndex               <- inEnv $ lookupDecArg helperName
  Just decArg' <- inEnv $ lookupIdent ValueScope (argNames !! decArgIndex)
  return
    (G.FixBody qualid
               (NonEmpty.fromList binders)
               (Just (G.StructOrder decArg'))
               returnType'
               expr'
    )
