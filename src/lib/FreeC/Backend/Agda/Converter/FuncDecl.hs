-- | This module contains functions for generating Agda function declarations
--   from our intermediate representation.

module FreeC.Backend.Agda.Converter.FuncDecl
  ( convertFuncDecls
  )
where

import           Data.Maybe                     ( fromJust )

import           FreeC.Backend.Agda.Converter.Arg
                                                ( convertTypeVarDecl )
import           FreeC.Backend.Agda.Converter.Free
                                                ( addFreeArgs )
import           FreeC.Backend.Agda.Converter.Type
                                                ( convertFuncType )
import qualified FreeC.Backend.Agda.Syntax     as Agda
import           FreeC.Backend.Coq.Analysis.DecreasingArguments
                                                ( identifyDecArgs )
import           FreeC.Environment.LookupOrFail
import           FreeC.IR.DependencyGraph
import qualified FreeC.IR.Syntax               as IR
import qualified FreeC.LiftedIR.Converter.Type as LIR
import           FreeC.Monad.Converter          ( Converter
                                                , localEnv
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
--   type signature and the definition (TODO).
convertFuncDecl :: IR.FuncDecl -> Maybe Int -> Converter [Agda.Declaration]
convertFuncDecl decl decArg =
  localEnv $ sequence [convertSignature decl decArg]

-- | Converts the type signature of the given function to an Agda type
--   declaration.
convertSignature :: IR.FuncDecl -> Maybe Int -> Converter Agda.Declaration
convertSignature (IR.FuncDecl _ declIdent typeVars args returnType _) decArg =
  do
    let IR.DeclIdent srcSpan name = declIdent
    let argTypes                  = map IR.varPatType args
    ident <- lookupUnQualAgdaIdentOrFail srcSpan IR.ValueScope name
    Agda.funcSig ident <$> convertFunc decArg typeVars argTypes returnType

-- | Converts a fully applied function.
convertFunc
  :: Maybe Int        -- ^ The index of the decreasing argument.
  -> [IR.TypeVarDecl] -- ^ Type variables bound by the function declaration.
  -> [Maybe IR.Type]  -- ^ The types of the arguments.
  -> Maybe IR.Type    -- ^ The return type of the function.
  -> Converter Agda.Expr
convertFunc decArg tVars argTypes returnType =
  Agda.pi . addFreeArgs <$> mapM convertTypeVarDecl tVars <*> typeConverter
    (map fromJust argTypes)
    (LIR.convertType $ fromJust returnType)
  where typeConverter ts = convertFuncType (LIR.convertFuncArgTypes decArg ts)
