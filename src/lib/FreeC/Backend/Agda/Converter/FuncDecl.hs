-- | This module contains functions for generating Agda function declarations
--   from our intermediate representation.

module FreeC.Backend.Agda.Converter.FuncDecl
  ( convertFuncDecl
  )
where

import           Data.Maybe                     ( fromJust )

import           FreeC.Backend.Agda.Converter.Arg
                                                ( convertTypeVarDecl )
import           FreeC.Backend.Agda.Converter.Free
                                                ( addFreeArgs )
import           FreeC.Backend.Agda.Converter.Type
                                                ( convertFuncType
                                                , convertRecFuncType
                                                )
import qualified FreeC.Backend.Agda.Syntax     as Agda
import           FreeC.Environment              ( lookupDecArgIndex )
import           FreeC.Environment.LookupOrFail
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter          ( Converter
                                                , localEnv
                                                , inEnv
                                                )

-- | Converts the given function declarations. Returns the declarations for the
--   type signature and the definition (TODO).
convertFuncDecl :: IR.FuncDecl -> Converter [Agda.Declaration]
convertFuncDecl decl = localEnv $ sequence [convertSignature decl]

-- | Converts the type signature of the given function to an Agda type
--   declaration.
convertSignature :: IR.FuncDecl -> Converter Agda.Declaration
convertSignature (IR.FuncDecl _ (IR.DeclIdent srcSpan name) typeVars args returnType _)
  = do
    let types = map IR.varPatType args
    let ident = lookupUnQualAgdaIdentOrFail srcSpan IR.ValueScope name
    decArg <- inEnv $ lookupDecArgIndex name
    Agda.funcSig <$> ident <*> convertFunc decArg typeVars types returnType

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
    (fromJust returnType)
  where typeConverter = maybe convertFuncType convertRecFuncType decArg

