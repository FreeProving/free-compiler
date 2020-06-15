-- | This module contains functions for generating Agda function, constructor
--   and type arguments from our intermediate representation.

module FreeC.Backend.Agda.Converter.Arg
  ( convertTypeVarDecl
  , lookupIdent
  , lookupValueIdent
  , lookupTypeIdent
  , lookupSmartIdent
  )
where

import qualified FreeC.Backend.Agda.Syntax     as Agda
import           FreeC.Environment.LookupOrFail ( lookupAgdaIdentOrFail
                                                , lookupAgdaSmartIdentOrFail
                                                )
import           FreeC.Environment.Renamer      ( renameAndDefineAgdaTypeVar )
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter          ( Converter )


-- | Utility function for introducing a new Agda type variable to the current
--   scope.
convertTypeVarDecl :: IR.TypeVarDecl -> Converter Agda.Name
convertTypeVarDecl (IR.TypeVarDecl srcSpan name) =
  Agda.unqualify <$> renameAndDefineAgdaTypeVar srcSpan name

-- | Looks up an IR identifier in the environment and converts it to an
--   unqualified Agda name.
lookupIdent :: IR.Scope -> IR.DeclIdent -> Converter Agda.Name
lookupIdent scope (IR.DeclIdent srcSpan name) =
  Agda.unqualify <$> lookupAgdaIdentOrFail srcSpan scope name

-- | Looks up the name of a Haskell function in the environment and converts
--   it to an Agda name.
lookupValueIdent :: IR.DeclIdent -> Converter Agda.Name
lookupValueIdent = lookupIdent IR.ValueScope

-- | Looks up the name of a Haskell data type in the environment and converts
--   it to an Agda name.
lookupTypeIdent :: IR.DeclIdent -> Converter Agda.Name
lookupTypeIdent = lookupIdent IR.TypeScope

-- | Looks up the name of a smart constructor for a Haskell data type in the
--   environment and converts it to an Agda name.
lookupSmartIdent :: IR.DeclIdent -> Converter Agda.Name
lookupSmartIdent (IR.DeclIdent srcSpan name) =
  Agda.unqualify <$> lookupAgdaSmartIdentOrFail srcSpan name
