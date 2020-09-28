-- | This module contains functions for generating Agda function, constructor
--   and type arguments from our intermediate representation.
module FreeC.Backend.Agda.Converter.Arg ( convertTypeVarDecl, convertArg ) where

import qualified FreeC.Backend.Agda.Syntax as Agda
import           FreeC.Environment.Renamer
  ( renameAndDefineAgdaTypeVar, renameAndDefineAgdaVar )
import qualified FreeC.IR.Syntax           as IR
import           FreeC.Monad.Converter     ( Converter )

-- | Utility function for introducing a new Agda type variable to the current
--   scope.
convertTypeVarDecl :: IR.TypeVarDecl -> Converter Agda.Name
convertTypeVarDecl (IR.TypeVarDecl srcSpan name)
  = Agda.unqualify <$> renameAndDefineAgdaTypeVar srcSpan name

-- | Converts a given 'IR.VarPat' by defining a new Agda variable with the
--   same name in the current scope.
convertArg :: IR.VarPat -> Converter Agda.QName
convertArg (IR.VarPat srcSpan ident maybeArgType isStrict)
  = renameAndDefineAgdaVar srcSpan isStrict ident maybeArgType
