-- | This module contains functions for converting function declarations from
--   Haskell to Coq.

module Compiler.Converter.FuncDecl where

import           Control.Monad                  ( mapAndUnzipM
                                                , zipWithM
                                                )
import           Data.List                      ( elemIndex )
import qualified Data.List.NonEmpty            as NonEmpty
import           Data.Maybe                     ( fromJust )
import qualified Data.Set                      as Set
import           Data.Set                       ( Set )

import           Compiler.Analysis.DependencyAnalysis
import           Compiler.Analysis.DependencyExtraction
import           Compiler.Analysis.RecursionAnalysis
import           Compiler.Converter.Arg
import           Compiler.Converter.Expr
import           Compiler.Converter.Free
import           Compiler.Converter.Type
import qualified Compiler.Coq.AST              as G
import           Compiler.Environment
import           Compiler.Environment.Fresh
import           Compiler.Environment.LookupOrFail
import           Compiler.Environment.Renamer
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
convertFuncComponent :: DependencyComponent -> Converter [G.Sentence]
convertFuncComponent (NonRecursive decl) = do
  decl' <- convertNonRecFuncDecl decl
  return [decl']
convertFuncComponent (Recursive decls) = do
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
  :: HS.Name       -- ^ The name of the function.
  -> [HS.VarPat]   -- ^ The function argument patterns.
  -> Converter (G.Qualid, [G.Binder], Maybe G.Term)
convertFuncHead name args = do
  -- Lookup the Coq name of the function.
  Just qualid <- inEnv $ lookupIdent VarScope name
    -- Lookup type signature and partiality.
  partial     <- inEnv $ isPartial name
  Just (usedTypeVars, argTypes, returnType) <- inEnv
    $ lookupArgTypes VarScope name
  -- Convert arguments and return type.
  typeVarDecls' <- generateTypeVarDecls G.Implicit usedTypeVars
  decArgIndex   <- inEnv $ lookupDecArg name
  args'         <- convertArgs args argTypes decArgIndex
  returnType'   <- mapM convertType returnType
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
defineFuncDecl :: HS.Decl -> Converter ()
defineFuncDecl (HS.FuncDecl _ (HS.DeclIdent srcSpan ident) args _) = do
  -- TODO detect redefinition and inform when renamed
  let name = HS.Ident ident
  funcType <- lookupTypeSigOrFail srcSpan name
  (argTypes, returnType) <- splitFuncType name args funcType
  _ <- renameAndDefineFunc ident (map Just argTypes) (Just returnType)
  return ()

-- | Splits the annotated type of a Haskell function with the given arguments
--   into its argument and return types.
--
--   Type synonyms are expanded if neccessary.
splitFuncType
  :: HS.Name     -- ^ The name of the function to display in error messages.
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
convertNonRecFuncDecl :: HS.Decl -> Converter G.Sentence
convertNonRecFuncDecl decl@(HS.FuncDecl _ (HS.DeclIdent _ ident) args expr) =
  do
    defineFuncDecl decl
    localEnv $ do
      let name = HS.Ident ident
      (qualid, binders, returnType') <- convertFuncHead name args
      expr'                          <- convertExpr expr
      return (G.definitionSentence qualid binders returnType' expr')

-------------------------------------------------------------------------------
-- Recursive function declarations                                           --
-------------------------------------------------------------------------------

-- | Converts (mutually) recursive Haskell function declarations to Coq.
convertRecFuncDecls :: [HS.Decl] -> Converter [G.Sentence]
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
    inlinedHelperDecl <- inlineDecl mainDecls helperDecl
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
transformRecFuncDecl :: HS.Decl -> DecArgIndex -> Converter ([HS.Decl], HS.Decl)
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
  name :: HS.Name
  name = HS.Ident (HS.fromDeclIdent declIdent)

  -- | The names of the function's arguments.
  argNames :: [HS.Name]
  argNames = map (HS.Ident . HS.fromVarPat) args

  -- | The name of the decreasing argument.
  decArg :: HS.Name
  decArg = argNames !! decArgIndex

  -- | The positions of @case@-expressions for the decreasing argument.
  --
  --   TODO restrict to outermost positions.
  caseExprsPos :: [Pos]
  caseExprsPos = filter decArgNotShadowed (findSubtermPos isCaseExpr expr)

  -- | Tests whether the given expression is a @case@-expression for the
  --   the decreasing argument.
  isCaseExpr :: HS.Expr -> Bool
  isCaseExpr (HS.Case _ (HS.Var _ name) _) = name == decArg
  isCaseExpr _                             = False

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
  generateHelperDecl :: Pos -> Converter (HS.Decl, HS.Expr)
  generateHelperDecl caseExprPos = do
    -- Generate a fresh name for the helper function.
    helperIdent <- freshHaskellIdent (HS.fromDeclIdent declIdent)
    let helperName      = HS.Ident helperIdent
        helperDeclIdent = HS.DeclIdent (HS.getSrcSpan declIdent) helperIdent

    -- Pass used variables as additional arguments to the helper function.
    let usedVars = Set.toList (usedVarsAt expr caseExprPos)
        helperArgs =
          args
            ++ map (HS.VarPat NoSrcSpan . fromJust . HS.identFromName) usedVars

    -- Build helper function declaration and application.
    let (Just caseExpr) = selectSubterm expr caseExprPos
        helperDecl = HS.FuncDecl srcSpan helperDeclIdent helperArgs caseExpr
        helperApp = HS.app NoSrcSpan
                           (HS.Var NoSrcSpan helperName)
                           (map (HS.Var NoSrcSpan) (argNames ++ usedVars))

    -- Register the helper function to the environment.
    -- The type of the helper function is the same as of the original function.
    -- Additionally we need to remember the index of the decreasing argument
    -- (see 'convertDecArg').
    funcType               <- lookupTypeSigOrFail srcSpan name
    (argTypes, returnType) <- splitFuncType name args funcType
    _                      <- renameAndDefineFunc
      helperIdent
      (map Just argTypes ++ replicate (length usedVars) Nothing)
      (Just returnType)
    modifyEnv $ defineDecArg helperName decArgIndex

    return (helperDecl, helperApp)

-- | Converts a recursive helper function to the body of a Coq @Fixpoint@
--   sentence.
convertRecHelperFuncDecl :: HS.Decl -> Converter G.FixBody
convertRecHelperFuncDecl (HS.FuncDecl _ declIdent args expr) = localEnv $ do
  let helperName = HS.Ident (HS.fromDeclIdent declIdent)
      argNames   = map (HS.Ident . HS.fromVarPat) args
  (qualid, binders, returnType') <- convertFuncHead helperName args
  expr'                          <- convertExpr expr
  Just decArgIndex               <- inEnv $ lookupDecArg helperName
  Just decArg' <- inEnv $ lookupIdent VarScope (argNames !! decArgIndex)
  return
    (G.FixBody qualid
               (NonEmpty.fromList binders)
               (Just (G.StructOrder decArg'))
               returnType'
               expr'
    )
