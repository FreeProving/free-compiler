-- | This module contains functions for generating Agda function declarations
--   from our intermediate representation.

module FreeC.Backend.Agda.Converter.FuncDecl
  ( convertFuncDecl
  )
where

import           Prelude                 hiding ( mod )

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
convertSignature (IR.FuncDecl _ (IR.DeclIdent s name) tVars args rType _) = do
  decArg <- inEnv $ lookupDecArgIndex name
  Agda.funcSig <$> ident <*> convertFunc decArg tVars types rType
 where
  types = map IR.varPatType args
  ident = lookupUnQualAgdaIdentOrFail s IR.ValueScope name

-- | Converts a fully applied function.
convertFunc
  :: Maybe Int
  -> [IR.TypeVarDecl]
  -> [Maybe IR.Type]
  -> Maybe IR.Type
  -> Converter Agda.Expr
convertFunc decArg tVars ts rt = do
  Agda.pi . addFreeArgs <$> mapM convertTypeVarDecl tVars <*> maybe
    convertFuncType
    convertRecFuncType
    decArg
    (map fromJust ts)
    (fromJust rt)
