-- | This module contains functions for generating Agda function declarations
--   from our intermediate representation.

module FreeC.Backend.Agda.Converter.FuncDecl
  ( convertFuncDecl
  )
where

import           Prelude                 hiding ( mod )

import           Data.Maybe                     ( fromJust )

import           FreeC.Backend.Agda.Converter.Free
                                                ( addFreeArgs )
import           FreeC.Backend.Agda.Converter.Type
                                                ( convertFunctionType
                                                , renameAgdaTypeVar
                                                )
import qualified FreeC.Backend.Agda.Syntax     as Agda
import           FreeC.Environment.LookupOrFail ( lookupAgdaIdentOrFail )
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter          ( Converter
                                                , localEnv
                                                )

-- | Converts the given function declarations. Returns the declarations for the
--   type signature and the definition (TODO).
convertFuncDecl :: IR.FuncDecl -> Converter [Agda.Declaration]
convertFuncDecl decl = localEnv $ sequence [convertSignature decl]

-- | Converts the type signature of the given function to an Agda type
--   declaration.
convertSignature :: IR.FuncDecl -> Converter Agda.Declaration
convertSignature (IR.FuncDecl _ ident tVars args retType _) =
  Agda.funcSig <$> lookupValueIdent ident <*> convertFunc_ tVars types retType
  where types = map IR.varPatType args

-- | Looks up the name of a Haskell function in the environment and converts it
--   to an Agda name.
lookupValueIdent :: IR.DeclIdent -> Converter Agda.Name
lookupValueIdent (IR.DeclIdent srcSpan name) =
  Agda.unqualify <$> lookupAgdaIdentOrFail srcSpan IR.ValueScope name

-- | Converts a fully applied function.
convertFunc_
  :: [IR.TypeVarDecl] -> [Maybe IR.Type] -> Maybe IR.Type -> Converter Agda.Expr
convertFunc_ tVars ts rt =
  --fromJust handled in #19
                           Agda.pi <$> tVars' <*> convertFunctionType
  (map fromJust ts)
  (fromJust rt)
  where tVars' = addFreeArgs <$> mapM renameAgdaTypeVar tVars
