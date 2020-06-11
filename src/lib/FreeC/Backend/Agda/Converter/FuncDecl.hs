-- | This module contains functions for generating Agda function declarations
--   from our intermediate representation.

module FreeC.Backend.Agda.Converter.FuncDecl
  ( convertFuncDecl
  )
where

import           Prelude                 hiding ( mod )

import           Data.List.Extra                ( snoc )
import           Data.Maybe                     ( fromJust )

import           FreeC.Backend.Agda.Converter.Arg
                                                ( convertTypeVarDecl
                                                , lookupValueIdent
                                                )
import           FreeC.Backend.Agda.Converter.Free
                                                ( addFreeArgs )
import           FreeC.Backend.Agda.Converter.Type
                                                ( convertFunctionType )
import qualified FreeC.Backend.Agda.Syntax     as Agda
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
  Agda.funcSig <$> lookupValueIdent ident <*> convertFunc_ tVars types
  where types = (IR.varPatType `map` args) `snoc` retType

-- | Converts a fully applied function.
convertFunc_ :: [IR.TypeVarDecl] -> [Maybe IR.Type] -> Converter Agda.Expr
convertFunc_ tVars ts = Agda.pi <$> tVars' <*> convertFunctionType
  (fromJust `map` ts) -- handled in #19
  where tVars' = addFreeArgs <$> mapM convertTypeVarDecl tVars

