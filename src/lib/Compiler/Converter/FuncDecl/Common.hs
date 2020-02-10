-- | This function contains auxilary functions that are used both to translate
--   recursive and non-recursive Haskell functions to Coq.

module Compiler.Converter.FuncDecl.Common
  ( -- * Type inference
    inferAndInsertTypeSigs
  , splitFuncType
    -- * Function environment entries
  , defineFuncDecl
    -- * Code generation
  , convertFuncHead
  )
where

import           Control.Monad.Extra            ( zipWithM_ )

import           Compiler.Analysis.PartialityAnalysis
import           Compiler.Analysis.TypeInference
import           Compiler.Converter.Arg
import           Compiler.Converter.Free
import           Compiler.Converter.Type
import qualified Compiler.Coq.AST              as G
import           Compiler.Environment
import           Compiler.Environment.Entry
import           Compiler.Environment.LookupOrFail
import           Compiler.Environment.Renamer
import           Compiler.Environment.Scope
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.Inliner
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty

-------------------------------------------------------------------------------
-- Type inference                                                            --
-------------------------------------------------------------------------------

-- | Infers the types of the given function declarations and inserts type
--   signatures into the environment.
--
--   Returns the function declarations where the type arguments of all function
--   and constructor applications on the right-hand side are applied visibly.
inferAndInsertTypeSigs :: [HS.FuncDecl] -> Converter [HS.FuncDecl]
inferAndInsertTypeSigs funcDecls = do
  (funcDecls', typeSchemas) <- addTypeAppExprsToFuncDecls' funcDecls
  zipWithM_ insertTypeSig funcDecls' typeSchemas
  return funcDecls'

-- Inserts a type signature for a function declaration of the given type into
-- the environment.
insertTypeSig :: HS.FuncDecl -> HS.TypeSchema -> Converter ()
insertTypeSig funcDecl typeSchema = do
  let name = HS.UnQual (HS.Ident (HS.fromDeclIdent (HS.getDeclIdent funcDecl)))
  modifyEnv $ defineTypeSig name typeSchema

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
-- Function environment entries                                              --
-------------------------------------------------------------------------------

-- | Inserts the given function declaration into the current environment.
defineFuncDecl :: HS.FuncDecl -> Converter ()
defineFuncDecl decl@(HS.FuncDecl srcSpan (HS.DeclIdent _ ident) args _) = do
  let name = HS.UnQual (HS.Ident ident)
  (HS.TypeSchema _ typeArgs funcType) <- lookupTypeSigOrFail srcSpan name
  (argTypes, returnType)              <- splitFuncType name args funcType
  partial                             <- isPartialFuncDecl decl
  _                                   <- renameAndAddEntry FuncEntry
    { entrySrcSpan       = srcSpan
    , entryArity         = length argTypes
    , entryTypeArgs      = map HS.fromDeclIdent typeArgs
    , entryArgTypes      = map Just argTypes
    , entryReturnType    = Just returnType
    , entryNeedsFreeArgs = True
    , entryIsPartial     = partial
    , entryName          = HS.UnQual (HS.Ident ident)
    , entryIdent         = undefined -- filled by renamer
    }
  return ()

-------------------------------------------------------------------------------
-- Code generation                                                           --
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
  Just qualid   <- inEnv $ lookupIdent ValueScope name
  -- Generate arguments for free monad if they are not in scope.
  freeArgDecls  <- generateGenericArgDecls G.Explicit
  -- Lookup type signature and partiality.
  partial       <- inEnv $ isPartial name
  Just typeArgs <- inEnv $ lookupTypeArgs ValueScope name
  Just argTypes <- inEnv $ lookupArgTypes ValueScope name
  returnType    <- inEnv $ lookupReturnType ValueScope name
  -- Convert arguments and return type.
  typeArgs'     <- generateTypeVarDecls G.Implicit typeArgs
  decArgIndex   <- inEnv $ lookupDecArgIndex name
  args'         <- convertArgs args argTypes decArgIndex
  returnType'   <- mapM convertType returnType
  return
    ( qualid
    , (freeArgDecls ++ [ partialArgDecl | partial ] ++ typeArgs' ++ args')
    , returnType'
    )
