-- | This module contains a data type that encapsulates the state of
--   the compiler. There are also utility functions to modify the state and
--   retreive information stored in the state.

module Compiler.Environment
  (-- * Environment
    Environment
  , Scope(..)
  , emptyEnvironment
  , usedIdents
  -- * Freh identifiers
  , freshIdentCount
  -- * Inserting entries into the environment
  , definePartial
  , definePureVar
  , defineDecArg
  , defineTypeSig
  , defineTypeSynonym
  , defineIdent
  , defineArgTypes
  -- * Looking up entries from the environment
  , isFunction
  , isPartial
  , isPureVar
  , lookupDecArg
  , lookupIdent
  , lookupArgTypes
  , lookupArity
  , lookupTypeSig
  , lookupTypeSynonym
  -- * Shortcuts for inserting entries into the environment
  , defineTypeCon
  , defineTypeVar
  , defineCon
  , defineVar
  , defineFunc
  )
where

import           Data.Composition               ( (.:)
                                                , (.:.)
                                                )
import           Data.List                      ( nub )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( catMaybes
                                                , isJust
                                                )
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set
import           Data.Tuple.Extra               ( snd3 )

import           Compiler.Analysis.DependencyExtraction
import qualified Compiler.Coq.AST              as G
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Pretty

-------------------------------------------------------------------------------
-- Environment                                                               --
-------------------------------------------------------------------------------

-- | In Haskell type and function names live in separate scopes. Therefore we
--   need to qualify each name stored in the 'Environment' with the scope it
--   is defined in. There is an additional scope for smart constructors such
--   that multiple Coq identifiers can be associated with the same Haskell data
--   constructor name.
data Scope = TypeScope | ConScope | SmartConScope | VarScope
  deriving (Eq, Ord, Show)

-- | Gets a description of the entries in the given scope.
--
--   This pretty instance is used to generate human readable error messages.
instance Pretty Scope where
  pretty TypeScope     = prettyString "type"
  pretty ConScope      = prettyString "data constructor"
  pretty SmartConScope = prettyString "data constructor"
  pretty VarScope      = prettyString "function or variable"

-- | Type that is used by maps in the 'Environment' to qualify Haskell names
--   with the scopes they are defined in.
type ScopedName = (Scope, HS.Name)

-- | Data type that encapsulates the state of the converter.
data Environment = Environment
  { freshIdentCount :: Map String Int
    -- ^ The number of fresh identifiers that were used in the environment
    --   with a certain prefix.
  , partialFunctions :: Set HS.Name
    -- ^ The names of partial functions. This map also contains entries for
    --   functions that have not yet been defined and functions that are
    --   shadowed by local vairables.
  , pureVars :: Set HS.Name
    -- ^ The names of Haskell variables that are not monadic.
  , decArgs :: Map HS.Name Int
    -- ^ Maps Haskell function names to the index of their decreasing argument.
    --   Contains no entry for non-recursive functions, but there are also
    --   entries for functions that are shadowed by local variables.
  , definedIdents :: Map ScopedName G.Qualid
    -- ^ Maps Haskell names of defined functions, (type/smart) constructors and
    --  (type) variables to corresponding Coq identifiers.
  , definedArgTypes
      :: Map ScopedName ([HS.TypeVarIdent], [Maybe HS.Type], Maybe HS.Type)
    -- ^ Maps Haskell names of defined functions and (smart) constructors
    --   to their argument and return types. If the type of an argument or the
    --   return type is not known, @Nothing@ is stored instead. The first
    --   component contains the names of all type variables used in the argument
    --   and return types. There are no entries in this map for local variables
    --   or datatype declarations. However there are entries for type signatues
    --   (the annotated type is stored as the return type and the argument type
    --   list is empty).
  , definedTypeSynonyms :: Map HS.Name ([HS.TypeVarIdent], HS.Type)
    -- ^ Maps names of Haskell type synonyms to the type that is abbreviated
    --   by the type synonym and the type variables used by that type.
    --   There should also be an entry in 'definedIdents' for the type synonym.
  }
  deriving Show

-- | An environment that does not even contain any predefined types and
--   functions.
emptyEnvironment :: Environment
emptyEnvironment = Environment
  { freshIdentCount     = Map.empty
  , partialFunctions    = Set.empty
  , pureVars            = Set.empty
  , decArgs             = Map.empty
  , definedIdents       = Map.empty
  , definedArgTypes     = Map.empty
  , definedTypeSynonyms = Map.empty
  }

-- | Gets a list of Coq identifiers for functions, (type/smart) constructors,
--   (type/fresh) variables that were used in the given environment already.
usedIdents :: Environment -> [G.Qualid]
usedIdents = Map.elems . definedIdents

-------------------------------------------------------------------------------
-- Inserting entries into the environment                                    --
-------------------------------------------------------------------------------

-- | Inserts the given function name into the set of partial functions.
definePartial :: HS.Name -> Environment -> Environment
definePartial name env =
  env { partialFunctions = Set.insert name (partialFunctions env) }

-- | Inserts the given variable name into the set of non-monadic variables.
definePureVar :: HS.Name -> Environment -> Environment
definePureVar name env = env { pureVars = Set.insert name (pureVars env) }

-- | Stores the index of the decreasing argument of a recursive function
--   in the environment.
defineDecArg :: HS.Name -> Int -> Environment -> Environment
defineDecArg name index env =
  env { decArgs = Map.insert name index (decArgs env) }

-- | Associates the name of a Haskell function, (type/smart) constructor or
--   (type) variable with the given Coq identifier.
--
--   If there is an entry associated with the same name in the given scope
--   already, the entry is overwritten.
--
--   All information that is already associated with the identifier is shadowed
--   by this function (e.g. the argument and return types have to be set after
--   the identifier was inserted into the environment, see 'defineArgTypes').
defineIdent :: Scope -> HS.Name -> G.Qualid -> Environment -> Environment
defineIdent scope name ident env = env
  { definedIdents   = Map.insert (scope, name) ident (definedIdents env)
  , definedArgTypes = Map.delete (scope, name) (definedArgTypes env)
  }

-- | Associates the name of a Haskell function or (smart) constructor with its
--   argument and return types.
defineArgTypes
  :: Scope             -- ^ The scope of the name.
  -> HS.Name           -- ^ The name of the function or constructor.
  -> [Maybe HS.Type]   -- ^ The known types of the arguments.
  -> Maybe HS.Type     -- ^ The return type.
  -> Environment
  -> Environment
defineArgTypes scope name argTypes returnType env = env
  { definedArgTypes = Map.insert (scope, name)
                                 (usedTypeVars, argTypes, returnType)
                                 (definedArgTypes env)
  }
 where
  -- | The type variables used by the (knonw) argument and return types.
  usedTypeVars :: [HS.TypeVarIdent]
  usedTypeVars =
    nub $ catMaybes $ map HS.identFromName $ concatMap typeVars $ catMaybes
      (argTypes ++ [returnType])

-- | Associates the name of a Haskell function with it's annoated type.
--
--   If there is an entry associated with the same name already, the entry
--   is overwritten.
--
--   Type signatures are defined after all data type declarations have been
--   defined but before any function declaration is converted. When a function
--   is converted it splits the annotated type into argument and return types
--   and replaces the entry created by this function.
defineTypeSig :: HS.Name -> HS.Type -> Environment -> Environment
defineTypeSig name typeExpr = defineArgTypes VarScope name [] (Just typeExpr)

-- | Associates the name of a Haskell type synonym with the type that is
--   abbreviated by the type synonym.
defineTypeSynonym
  :: HS.Name           -- ^ The name of the type synonym.
  -> [HS.TypeVarIdent] -- ^ The type variables of the type synonym.
  -> HS.Type           -- ^ The abbreviated type.
  -> Environment
  -> Environment
defineTypeSynonym name usedTypeVars typeExpr env = env
  { definedTypeSynonyms = Map.insert name
                                     (usedTypeVars, typeExpr)
                                     (definedTypeSynonyms env)
  }

-------------------------------------------------------------------------------
-- Looking up entries from the environment                                   --
-------------------------------------------------------------------------------

-- | Tests whether the given name identifies a function in the given
--   environment.
--
--   Returns @False@ if there is no such function.
isFunction :: HS.Name -> Environment -> Bool
isFunction = isJust .: lookupArgTypes VarScope

-- | Tests whether the function with the given name is partial.
--
--   Returns @False@ if there is no such function.
isPartial :: HS.Name -> Environment -> Bool
isPartial name = Set.member name . partialFunctions

-- | Test whether the variable with the given name is not monadic.
isPureVar :: HS.Name -> Environment -> Bool
isPureVar name = Set.member name . pureVars

-- | Lookups the index of the decreasing argument of the recursive function
--   with the given name.
--
--   Returns @Nothing@ if there is no such recursive function.
lookupDecArg :: HS.Name -> Environment -> Maybe Int
lookupDecArg name = Map.lookup name . decArgs

-- | Looks up the Coq identifier for a Haskell function, (type/smart)
--   constructor or (type) variable with the given name.
--
--   Returns @Nothing@ if there is no such function, (type/smart) constructor,
--   constructor or (type) variable with the given name.
lookupIdent :: Scope -> HS.Name -> Environment -> Maybe G.Qualid
lookupIdent scope name = Map.lookup (scope, name) . definedIdents

-- | Looks up the argument and return types of the function or (smart)
--   constructor with the given name.
--
--   Returns @Nothing@ if there is no such function or (smart) constructor
--   with the given name.
lookupArgTypes
  :: Scope
  -> HS.Name
  -> Environment
  -> Maybe ([HS.TypeVarIdent], [Maybe HS.Type], Maybe HS.Type)
lookupArgTypes scope name = Map.lookup (scope, name) . definedArgTypes

-- | Looks up the number of arguments expected by the Haskell function
--   or smart constructor with the given name.
--
--   Returns @Nothing@ if there is no such function or (smart) constructor
--   with the given name.
lookupArity :: Scope -> HS.Name -> Environment -> Maybe Int
lookupArity = fmap (length . snd3) .:. lookupArgTypes

-- | Looks up the annotated type of a user defined Haskell function with the
--   given name.
--
--   This function assumes that the type signature has been insered into the
--   environment using 'defineTypeSig' and the entry has not yet been replaced.
--
--   Returns @Nothing@, if there is no such type signature or the entry has
--   been replaced already.
lookupTypeSig :: HS.Name -> Environment -> Maybe HS.Type
lookupTypeSig name env = do
  (_, [], Just returnType) <- lookupArgTypes VarScope name env
  return returnType

-- | Looks up the type the type synonym with the given name is associated with.
--
--   Returns @Nothing@ if there is no such type synonym.
lookupTypeSynonym
  :: HS.Name -> Environment -> Maybe ([HS.TypeVarIdent], HS.Type)
lookupTypeSynonym name = Map.lookup name . definedTypeSynonyms

-------------------------------------------------------------------------------
-- Shortcuts for inserting entries into the environment                      --
-------------------------------------------------------------------------------

-- | Associates the name of a Haskell type constructor with the corresponding
--   Coq identifier in the given environment.
--
--   If a type constructor with the same name exists, the entry is overwritten.
defineTypeCon
  :: HS.Name  -- ^ The Haskell name of the type constructor.
  -> Int      -- ^ The number of expected type arguments.
  -> G.Qualid -- ^ The Coq identifier for the type constructor.
  -> Environment
  -> Environment
defineTypeCon name _arity ident = defineIdent TypeScope name ident

-- | Associates the name of a Haskell type variable with the corresponding Coq
--   identifier in the given environment.
--
--   If a type variable with the same name exists, the entry is overwritten.
defineTypeVar :: HS.Name -> G.Qualid -> Environment -> Environment
defineTypeVar = defineIdent TypeScope

-- | Associates the name of a Haskell data constructor with the corresponding
--   Coq identifiers for the constructor and smart constructor in the given
--   environment.
--
--   If a constructor with the same name exists, the entry is overwritten.
defineCon
  :: HS.Name  -- ^ The Haskell name of the constructor.
  -> G.Qualid -- ^ The Coq identifier for the data constructor.
  -> G.Qualid -- ^ The Coq identifier for the smart constructor.
  -> [Maybe HS.Type] -- ^ The types of the function's arguments (if known).
  -> Maybe HS.Type   -- ^ The function's return type (if knonw).
  -> Environment
  -> Environment
defineCon name ident smartIdent argTypes returnType =
  defineArgTypes ConScope name argTypes returnType
    . defineArgTypes SmartConScope name argTypes returnType
    . defineIdent ConScope      name ident
    . defineIdent SmartConScope name smartIdent

-- | Associates the name of a Haskell variable with the corresponding Coq
--   identifier in the given environment.
--
--   If a function or variable with the same name exists, the entry is
--   overwritten.
defineVar
  :: HS.Name    -- ^ The Haskell name of the variable.
  -> G.Qualid   -- ^ The Coq identifier for the variable.
  -> Environment
  -> Environment
defineVar = defineIdent VarScope

-- | Associates the name of a Haskell function with the corresponding Coq
--   identifier in the given environment.
--
--   If a function or variable with the same name exists, the entry is
--   overwritten.
defineFunc
  :: HS.Name         -- ^ The Haskell name of the function.
  -> G.Qualid        -- ^ The Coq identifier of the function.
  -> [Maybe HS.Type] -- ^ The types of the function's arguments (if known).
  -> Maybe HS.Type   -- ^ The function's return type (if knonw).
  -> Environment
  -> Environment
defineFunc name ident argTypes returnType =
  defineArgTypes VarScope name argTypes returnType
    . defineIdent VarScope name ident
