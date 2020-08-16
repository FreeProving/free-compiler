-- | This module contains data types that are used to store information
--   about declared functions, (type) variables and (type) constructors
--   in the environment.
module FreeC.Environment.Entry where

import           Data.Function             ( on )
import           Data.Tuple.Extra          ( (&&&) )

import qualified FreeC.Backend.Agda.Syntax as Agda
import qualified FreeC.Backend.Coq.Syntax  as Coq
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax           as IR
import           FreeC.Util.Predicate

-- | Entry of the environment.
data EnvEntry
  = -- | Entry for a data type declaration.
    DataEntry
      { entrySrcSpan   :: SrcSpan
        -- ^ The source code location where the data type was declared.
      , entryArity     :: Int
        -- ^ The number of type arguments expected by the type constructor.
      , entryIdent     :: Coq.Qualid
        -- ^ The name of the data type in Coq.
      , entryAgdaIdent :: Agda.QName
        -- ^ The name of the data type in Agda.
      , entryName      :: IR.QName
        -- ^ The name of the data type in the module it has been defined in.
      , entryConsNames :: [IR.ConName]
        -- ^ The names of the constructors of the data type.
      }
    -- | Entry for a type synonym declaration.
  | TypeSynEntry
      { entrySrcSpan   :: SrcSpan
        -- ^ The source code location where the type synonym was declared.
      , entryArity     :: Int
        -- ^ The number of type arguments expected by the type constructor.
      , entryTypeArgs  :: [IR.TypeVarIdent]
        -- ^ The names of the type arguments.
      , entryTypeSyn   :: IR.Type
        -- ^ The type that is abbreviated by this type synonym.
      , entryIdent     :: Coq.Qualid
        -- ^ The name of the type synonym in Coq.
      , entryAgdaIdent :: Agda.QName
        -- ^ The name of the type synonym in Agda.
      , entryName      :: IR.QName
        -- ^ The name of the type synonym in the module it has been defined in.
      }
    -- | Entry for a type variable.
  | TypeVarEntry
      { entrySrcSpan   :: SrcSpan
        -- ^ The source code location where the type variable was declared.
      , entryIdent     :: Coq.Qualid
        -- ^ The name of the type variable in Coq.
      , entryAgdaIdent :: Agda.QName
        -- ^ The name of the type variable in Agda.
      , entryName      :: IR.QName
        -- ^ The name of the type variable (must be unqualified).
      }
    -- | Entry for a data constructor.
  | ConEntry
      { entrySrcSpan        :: SrcSpan
        -- ^ The source code location where the data constructor was declared.
      , entryArity          :: Int
        -- ^ The number of arguments expected by the data constructor.
      , entryTypeArgs       :: [IR.TypeVarIdent]
        -- ^ The names of the type arguments.
      , entryArgTypes       :: [IR.Type]
        -- ^ The types of the constructor's arguments.
        --   Contains exactly 'entryArity' elements.
      , entryReturnType     :: IR.Type
        -- ^ The return type of the data constructor.
      , entryIdent          :: Coq.Qualid
        -- ^ The name of the regular data constructor in Coq.
      , entryAgdaIdent      :: Agda.QName
        -- ^ The name of the regular data constructor in Agda.
      , entrySmartIdent     :: Coq.Qualid
        -- ^ The name of the corresponding smart constructor in Coq.
      , entryAgdaSmartIdent :: Agda.QName
        -- ^ The name of the corresponding smart constructor in Agda.
      , entryName           :: IR.QName
        -- ^ The name of the data constructor in the module it has been
        --   defined in.
      }
    -- | Entry for a function declaration.
  | FuncEntry
      { entrySrcSpan       :: SrcSpan
        -- ^ The source code location where the function was declared.
      , entryArity         :: Int
        -- ^ The number of arguments expected by the function.
      , entryTypeArgs      :: [IR.TypeVarIdent]
        -- ^ The names of the type arguments.
      , entryArgTypes      :: [IR.Type]
        -- ^ The types of the function arguments.
        --   Contains exactly 'entryArity' elements.
      , entryStrictArgs    :: [Bool]
        -- ^ Whether each argument is strict.
        --   Contains exactly 'entryArity' elements.
      , entryReturnType    :: IR.Type
        -- ^ The return type of the function (if known).
      , entryNeedsFreeArgs :: Bool
        -- ^ Whether the arguments of the @Free@ monad need to be
        --   passed to the function.
      , entryIsPartial     :: Bool
        -- ^ Whether the function is partial, i.e., requires an instance of
        --   the @Partial@ type class when translated to Coq.
      , entryIdent         :: Coq.Qualid
        -- ^ The name of the function in Coq.
      , entryAgdaIdent     :: Agda.QName
        -- ^ The name of the function in Agda.
      , entryName          :: IR.QName
        -- ^ The name of the function in the module it has been defined in.
      }
    -- | Entry for a variable.
  | VarEntry { entrySrcSpan   :: SrcSpan
               -- ^ The source code location where the variable was declared.
             , entryIsPure    :: Bool
               -- ^ Whether the variable has not been lifted to the free monad.
             , entryIdent     :: Coq.Qualid
               -- ^ The name of the variable in Coq.
             , entryAgdaIdent :: Agda.QName
               -- ^ The name of the variable in Agda.
             , entryName      :: IR.QName
               -- ^ The name of the variable (must be unqualified).
             , entryType      :: Maybe IR.Type
               -- ^ The type of the variable (if known).
             }
    -- | Entry for fresh variables.
    --
    --   The purpose of these entries is to prevent two fresh variables with
    --   the same name to be issued for generated AST nodes that have no
    --   corresponding
  | FreshEntry { entryIdent     :: Coq.Qualid
                 -- ^ The renamed fresh Coq identifier.
               , entryAgdaIdent :: Agda.QName
                 -- ^ The name of the variable in Agda.
               , entryName      :: IR.QName
                 -- ^ The actual fresh identifier before renaming.
               }
 deriving Show

-------------------------------------------------------------------------------
-- Comparison                                                                --
-------------------------------------------------------------------------------
-- | Entries are identified by their original name.
instance Eq EnvEntry where
  (==) = (==) `on` entryScopedName

-- | Entries are ordered by their original name.
instance Ord EnvEntry where
  compare = compare `on` entryScopedName

-------------------------------------------------------------------------------
-- Getters                                                                   --
-------------------------------------------------------------------------------
-- | Gets the scope an entry needs to be defined in.
entryScope :: EnvEntry -> IR.Scope
entryScope DataEntry {}    = IR.TypeScope
entryScope TypeSynEntry {} = IR.TypeScope
entryScope TypeVarEntry {} = IR.TypeScope
entryScope ConEntry {}     = IR.ValueScope
entryScope FuncEntry {}    = IR.ValueScope
entryScope VarEntry {}     = IR.ValueScope
entryScope FreshEntry {}   = IR.FreshScope

-- | Gets the scope and name of the given entry.
entryScopedName :: EnvEntry -> IR.ScopedName
entryScopedName = entryScope &&& entryName

-------------------------------------------------------------------------------
-- Predicates                                                                --
-------------------------------------------------------------------------------
-- | Tests whether the given entry of the environment describes a data type.
isDataEntry :: EnvEntry -> Bool
isDataEntry DataEntry {} = True
isDataEntry _ = False

-- | Tests whether the given entry of the environment describes a type synonym.
isTypeSynEntry :: EnvEntry -> Bool
isTypeSynEntry TypeSynEntry {} = True
isTypeSynEntry _ = False

-- | Tests whether the given entry of the environment describes a type
--   variable.
isTypeVarEntry :: EnvEntry -> Bool
isTypeVarEntry TypeVarEntry {} = True
isTypeVarEntry _ = False

-- | Tests whether the given entry of the environment describes a data
--   constructor.
isConEntry :: EnvEntry -> Bool
isConEntry ConEntry {} = True
isConEntry _           = False

-- | Tests whether the given entry of the environment describes a function.
isFuncEntry :: EnvEntry -> Bool
isFuncEntry FuncEntry {} = True
isFuncEntry _ = False

-- | Tests whether the given entry of the environment describes a variable.
isVarEntry :: EnvEntry -> Bool
isVarEntry VarEntry {} = True
isVarEntry _           = False

-- | Tests whether the given entry of the environment describes a top-level
--   data type, type synonym, constructor or function.
--
--   Type variables and local variables are no top level entries.
isTopLevelEntry :: EnvEntry -> Bool
isTopLevelEntry = not . (isVarEntry .||. isTypeVarEntry)

-- | Tests whether the given entry distinguishes between a @entryIdent@ and
--   @entrySmartIdent@.
entryHasSmartIdent :: EnvEntry -> Bool
entryHasSmartIdent = isConEntry

-------------------------------------------------------------------------------
-- Pretty Printing                                                           --
-------------------------------------------------------------------------------
-- | Gets a human readable description of the entry type.
prettyEntryType :: EnvEntry -> String
prettyEntryType DataEntry {}    = "data type"
prettyEntryType TypeSynEntry {} = "type synonym"
prettyEntryType TypeVarEntry {} = "type variable"
prettyEntryType ConEntry {}     = "constructor"
prettyEntryType FuncEntry {}    = "function"
prettyEntryType VarEntry {}     = "variable"
prettyEntryType FreshEntry {}   = "fresh identifier"
