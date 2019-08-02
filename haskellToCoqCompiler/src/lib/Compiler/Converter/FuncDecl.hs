-- | This module contains functions for converting function declarations from
--   Haskell to Coq.

module Compiler.Converter.FuncDecl where

import           Control.Monad                  ( mapAndUnzipM )
import           Data.List                      ( elemIndex )
import qualified Data.List.NonEmpty            as NonEmpty

import           Compiler.Analysis.DependencyAnalysis
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
import           Compiler.Monad.Converter

-------------------------------------------------------------------------------
-- Strongly connected components                                             --
-------------------------------------------------------------------------------

-- | Converts a strongly connected component of the function dependency graph.
convertFuncComponent :: DependencyComponent -> Converter [G.Sentence]
convertFuncComponent (NonRecursive decl) = do
  decl' <- convertNonRecFuncDecl decl
  return [decl']
convertFuncComponent (Recursive decls) = convertRecFuncDecls decls

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
  let name  = HS.Ident ident
      arity = length args
  funcType <- lookupTypeSigOrFail srcSpan name
  (argTypes, returnType) <- splitFuncType funcType arity
  _ <- renameAndDefineFunc ident (map Just argTypes) (Just returnType)
  return ()

-- | Splits the annotated type of a Haskell function with the given arity into
--   its argument and return types.
--
--   A function with arity \(n\) has \(n\) argument types. TODO  Type synonyms
--   are expanded if neccessary.
splitFuncType :: HS.Type -> Int -> Converter ([HS.Type], HS.Type)
splitFuncType (HS.TypeFunc _ t1 t2) arity | arity > 0 = do
  (argTypes, returnType) <- splitFuncType t2 (arity - 1)
  return (t1 : argTypes, returnType)
splitFuncType funcType _ = return ([], funcType)

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
  (helperDecls, mainDecls) <- mapAndUnzipM transformRecFuncDecl decls
  fixBodies                <- mapM
    (localEnv . (>>= convertRecHelperFuncDecl) . inlineDecl mainDecls)
    (concat helperDecls)
  mainFunctions <- mapM convertNonRecFuncDecl mainDecls
  return
    ( -- TODO comment
      G.FixpointSentence (G.Fixpoint (NonEmpty.fromList fixBodies) [])
    : mainFunctions
    )

-- | Transforms the given recursive function declaration into recursive
--   helper functions and a non recursive main function.
transformRecFuncDecl :: HS.Decl -> Converter ([HS.Decl], HS.Decl)
transformRecFuncDecl (HS.FuncDecl srcSpan declIdent args expr) = do
  -- Identify decreasing argument of the function.
  (decArg, caseExprs, replaceCases) <- identifyDecArg expr

  -- Generate helper function declaration for each case expression of the
  -- decreasing argument.
  (helperNames, helperDecls)        <- mapAndUnzipM
    (uncurry (generateHelperDecl decArg))
    caseExprs

  -- Generate main function declaration. The main function's right hand side
  -- is constructed by replacing all case expressions of the decreasing
  -- argument by an invocation of the corresponding recursive helper function.
  let mainExpr =
        replaceCases (zipWith generateHelperApp helperNames (map fst caseExprs))
      mainDecl = HS.FuncDecl srcSpan declIdent args mainExpr

  return (helperDecls, mainDecl)
 where

  -- | The name of the function to transform.
  name :: HS.Name
  name = HS.Ident (HS.fromDeclIdent declIdent)

  -- | The names of the function's arguments.
  argNames :: [HS.Name]
  argNames = map (HS.Ident . HS.fromVarPat) args

  -- | Generates the recursive helper function declaration for the given
  --   @case@ expression that performs pattern matching on the given decreasing
  --   argument.
  generateHelperDecl
    :: HS.Name     -- ^ The name of the decreasing argument.
    -> [HS.VarPat] -- ^ The variable patterns of TODO.
    -> HS.Expr     -- ^ The @case@ expression.
    -> Converter (HS.Name, HS.Decl)
  generateHelperDecl decArg usedVars caseExpr = do
    helperIdent <- freshHaskellIdent (HS.fromDeclIdent declIdent)
    let
      helperName      = HS.Ident helperIdent
      helperDeclIdent = HS.DeclIdent (HS.getSrcSpan declIdent) helperIdent
      helperDecl =
        HS.FuncDecl srcSpan helperDeclIdent (args ++ usedVars) caseExpr
      (Just decArgIndex) = elemIndex decArg argNames

    -- Register the helper function to the environment.
    -- The type of the helper function is the same as of the original function.
    -- Additionally we need to remember the index of the decreasing argument
    -- (see 'convertDecArg').
    funcType               <- lookupTypeSigOrFail srcSpan name
    (argTypes, returnType) <- splitFuncType funcType (length args)
    _                      <- renameAndDefineFunc
      helperIdent
      (map Just argTypes ++ replicate (length usedVars) Nothing)
      (Just returnType)
    modifyEnv $ defineDecArg helperName decArgIndex

    return (helperName, helperDecl)

  -- | Generates the application expression for the helper function with the
  --   given name.
  generateHelperApp
    :: HS.Name     -- ^ The name of the helper function to apply.
    -> [HS.VarPat] -- ^ TODO
    -> HS.Expr
  generateHelperApp helperName usedVars = HS.app
    NoSrcSpan
    (HS.Var NoSrcSpan helperName)
    (  map (HS.Var NoSrcSpan)                            argNames
    ++ map (HS.Var NoSrcSpan . HS.Ident . HS.fromVarPat) usedVars
    )

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
