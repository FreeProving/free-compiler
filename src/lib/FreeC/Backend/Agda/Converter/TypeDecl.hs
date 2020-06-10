-- | This module contains functions for converting type synonym and data type
--   declarations and their constructors.

module FreeC.Backend.Agda.Converter.TypeDecl
  ( convertTypeDecl
  )
where

import qualified FreeC.IR.Syntax               as IR
import qualified FreeC.Backend.Agda.Syntax     as Agda
import           FreeC.Environment.LookupOrFail ( lookupAgdaIdentOrFail )
import           FreeC.Monad.Converter          ( Converter
                                                , localEnv
                                                )

convertTypeDecl :: IR.TypeDecl -> Converter Agda.Declaration
convertTypeDecl (IR.TypeSynDecl _ _ _ _) = error "Not Supported"
convertTypeDecl (IR.DataDecl _ ident _ constrs) =
  localEnv (Agda.dataDecl <$> lookupIdent ident <*> convertConstructors constrs)

-- unify with version from FuncDecl?
lookupIdent :: IR.DeclIdent -> Converter Agda.Name
lookupIdent (IR.DeclIdent srcSpan name) =
  Agda.unqualify <$> lookupAgdaIdentOrFail srcSpan IR.TypeScope name

convertConstructors :: [IR.ConDecl] -> Converter [Agda.Declaration]
convertConstructors = mapM convertConstructor

convertConstructor :: IR.ConDecl -> Converter Agda.Declaration
convertConstructor (IR.ConDecl _ ident types) = undefined
