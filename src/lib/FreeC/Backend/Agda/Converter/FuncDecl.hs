-- | This module contains functions for generating Agda function declarations
--   from our intermediate representation.

module FreeC.Backend.Agda.Converter.FuncDecl
  ( convertFuncDecls
  )
where


import           Control.Monad                  ( (>=>) )
import           Data.Maybe                     ( fromJust )

import           FreeC.Backend.Agda.Converter.Arg
                                                ( convertTypeVarDecl
                                                , convertArg
                                                )
import           FreeC.Backend.Agda.Converter.Expr
                                                ( convertLiftedExpr )
import           FreeC.Backend.Agda.Converter.Free
                                                ( addFreeArgs )
import           FreeC.Backend.Agda.Converter.Type
                                                ( convertLiftedFuncType )
import qualified FreeC.Backend.Agda.Syntax     as Agda
import           FreeC.Backend.Coq.Analysis.DecreasingArguments
                                                ( identifyDecArgs )
import           FreeC.Environment              ( isPartial )
import           FreeC.Environment.LookupOrFail
import           FreeC.IR.DependencyGraph
import qualified FreeC.IR.Syntax               as IR
import           FreeC.LiftedIR.Converter.Expr  ( convertExpr )
import           FreeC.LiftedIR.Converter.Type  ( liftFuncArgTypes
                                                , liftType
                                                )
import           FreeC.Monad.Converter          ( Converter
                                                , localEnv
                                                , inEnv
                                                )

-- | Converts a strongly connected component of the function dependency graph.
--   TODO: Handle mutually recursive functions.
convertFuncDecls
  :: DependencyComponent IR.FuncDecl -> Converter [Agda.Declaration]
convertFuncDecls (NonRecursive decl  ) = convertFuncDecl decl Nothing
convertFuncDecls (Recursive    [decl]) = do
  [decArg] <- identifyDecArgs [decl]
  convertFuncDecl decl $ Just decArg
convertFuncDecls (Recursive _) =
  error "Mutual recursive functions are not supported at the moment."

-- | Converts the given function declarations. Returns the declarations for the
--   type signature and the definition.
convertFuncDecl :: IR.FuncDecl -> Maybe Int -> Converter [Agda.Declaration]
convertFuncDecl decl decArg = sequence
  [localEnv $ convertSignature decl decArg, localEnv $ convertFuncDef decl]

------------------------------------------------------------------------------
-- Definitions                                                              --
------------------------------------------------------------------------------

-- | Converts the definition of the given function to an Agda function
--   declaration.
convertFuncDef :: IR.FuncDecl -> Converter Agda.Declaration
convertFuncDef (IR.FuncDecl _ (IR.DeclIdent srcSpan name) _ args _ expr) = do
  args' <- mapM convertArg args
  ident <- lookupAgdaIdentOrFail srcSpan IR.ValueScope name
  Agda.funcDef ident args' <$> (convertExpr >=> convertLiftedExpr) expr

------------------------------------------------------------------------------
-- Signatures                                                               --
------------------------------------------------------------------------------

-- | Converts the type signature of the given function to an Agda type
--   declaration.
convertSignature :: IR.FuncDecl -> Maybe Int -> Converter Agda.Declaration
convertSignature (IR.FuncDecl _ declIdent typeVars args returnType _) decArg =
  do
    let IR.DeclIdent srcSpan name = declIdent
    let argTypes                  = map IR.varPatType args
    partial <- inEnv $ isPartial name
    ident   <- lookupUnQualAgdaIdentOrFail srcSpan IR.ValueScope name
    Agda.funcSig ident
      <$> convertFunc decArg partial typeVars argTypes returnType

-- | Converts a fully applied function.
convertFunc
  :: Maybe Int        -- ^ The index of the decreasing argument.
  -> Bool             -- ^ Whether the function needs a @Partial@ instance.
  -> [IR.TypeVarDecl] -- ^ Type variables bound by the function declaration.
  -> [Maybe IR.Type]  -- ^ The types of the arguments.
  -> Maybe IR.Type    -- ^ The return type of the function.
  -> Converter Agda.Expr
convertFunc decArg partial tVars argTypes returnType =
  Agda.pi . addFreeArgs <$> mapM convertTypeVarDecl tVars <*> typeConverter
    (map fromJust argTypes)
    (liftType $ fromJust returnType)
 where
  typeConverter ts = convertLiftedFuncType partial (liftFuncArgTypes decArg ts)
