-- | This module contains functions for converting type synonym and data type
--   declarations and their constructors.

module FreeC.Backend.Agda.Converter.TypeDecl
  ( convertTypeDecl
  )
where

import qualified FreeC.IR.Syntax               as IR
import           FreeC.Backend.Agda.Converter.Free
import qualified FreeC.Backend.Agda.Syntax     as Agda
import           FreeC.Backend.Agda.Converter.Arg
                                                ( lookupTypeIdent
                                                , lookupValueIdent
                                                , convertTypeVarDecl
                                                )
import           FreeC.Monad.Converter          ( Converter
                                                , localEnv
                                                )

convertTypeDecl :: IR.TypeDecl -> Converter Agda.Declaration
convertTypeDecl (IR.TypeSynDecl _ _     _     _      ) = error "Not Supported"
convertTypeDecl (IR.DataDecl    _ ident tVars constrs) = localEnv
  (   freeDataDecl
  <$> lookupTypeIdent ident
  <*> mapM convertTypeVarDecl tVars
  <*> convertConstructors tVars constrs
  )

convertConstructors
  :: [IR.TypeVarDecl] -> [IR.ConDecl] -> Converter [Agda.Declaration]
convertConstructors tVars = mapM $ convertConstructor tVars

convertConstructor
  :: [IR.TypeVarDecl] -> IR.ConDecl -> Converter Agda.Declaration
convertConstructor types (IR.ConDecl _ ident _) =
  Agda.funcSig <$> lookupValueIdent ident <*> pure (Agda.intLiteral 42)
