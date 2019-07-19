{-# LANGUAGE GeneralizedNewtypeDeriving #-}

-- | This module contains a data type that encapsulates the state of
--   the converter and a state monad which allows the state to be passed
--   implicitly throught the converter.

module Compiler.Converter.State
  ( -- * Environment
    Environment
  , emptyEnvironment
  , definedIdents
  , defineFreshIdent
  , defineTypeCon
  , lookupTypeCon
  , defineTypeVar
  , lookupTypeVar
  , defineCon
  , lookupCon
  , lookupSmartCon
  , defineVar
  , defineFunc
  , lookupVar
    -- * State monad
  , Converter
  , runConverter
  , evalConverter
  , execConverter
    -- * Modifying environments
  , getEnv
  , inEnv
  , putEnv
  , modifyEnv
  , localEnv
  )
where

import           Control.Monad.Fail
import           Control.Monad.State
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map

import qualified Compiler.Language.Coq.AST     as G
import qualified Compiler.Language.Haskell.SimpleAST
                                               as HS
import           Compiler.Reporter

-------------------------------------------------------------------------------
-- Environment                                                               --
-------------------------------------------------------------------------------

-- | Data type that encapsulates the state of the converter.
data Environment = Environment
  { definedFreshIdents :: [G.Qualid]
    -- ^ The fresh Coq identifiers that were used already.
  , definedTypeCons :: Map HS.Name G.Qualid
    -- ^ Maps Haskell type constructor names to corresponding Coq identifiers.
  , definedTypeVars :: Map HS.Name G.Qualid
    -- ^ Maps Haskell type variable names to corresponding Coq identifiers.
  , definedCons :: Map HS.Name G.Qualid
  -- ^ Maps Haskell data constructor names to the Coq identifiers for the
  --   corresponding regular constructors.
  , definedSmartCons :: Map HS.Name G.Qualid
  -- ^ Maps Haskell data constructor names to the Coq identifiers for the
  --   corresponding smart constructors.
  , definedVars :: Map HS.Name G.Qualid
    -- ^ Maps Haskell function and variable names to corresponding Coq
    --   identifiers.
  , typeConArities :: Map HS.Name Int
    -- ^ Maps Haskell type constructor names to the number of expected
    --   arguments.
  , conArities :: Map HS.Name Int
    -- ^ Maps Haskell data constructor names to the number of expected
    --   arguments.
  , varArities :: Map HS.Name Int
    -- ^ Maps Haskell function and variable names to the number of expected
    --   arguments. The arity of variables should always be @0@.
  }
  deriving Show

-- | An environment that does not even contain any predefined types and
--   functions.
emptyEnvironment :: Environment
emptyEnvironment = Environment
  { definedFreshIdents = []
  , definedTypeCons    = Map.empty
  , definedTypeVars    = Map.empty
  , definedCons        = Map.empty
  , definedSmartCons   = Map.empty
  , definedVars        = Map.empty
  , typeConArities     = Map.empty
  , conArities         = Map.empty
  , varArities         = Map.empty
  }

-- | Gets a list of Coq identifiers for type constructors and variables,
--   smart and data consturctors, functions and variables that were
--   used in the given environment already.
definedIdents :: Environment -> [G.Qualid]
definedIdents env =
  definedFreshIdents env
    ++ Map.elems (definedTypeCons env)
    ++ Map.elems (definedTypeVars env)
    ++ Map.elems (definedCons env)
    ++ Map.elems (definedSmartCons env)
    ++ Map.elems (definedVars env)

-- | Adds the given fresh Coq identifier to the given environment.
defineFreshIdent :: G.Qualid -> Environment -> Environment
defineFreshIdent ident env =
  env { definedFreshIdents = ident : definedFreshIdents env }

-- | Associates the name of a Haskell type constructor with the corresponding
--   Coq identifier in the given environment.
--
--   If a type constructor with the same name exists, the entry is overwritten.
defineTypeCon :: HS.Name -> Int -> G.Qualid -> Environment -> Environment
defineTypeCon name arity ident env = env
  { definedTypeCons = Map.insert name ident (definedTypeCons env)
  , typeConArities  = Map.insert name arity (typeConArities env)
  }

-- | Looks up the Coq identifier for a Haskell type constructor with the given
--   name in the provided environment.
--
--   Returns @Nothing@ if there is no such type constructor.
lookupTypeCon :: HS.Name -> Environment -> Maybe G.Qualid
lookupTypeCon name = Map.lookup name . definedTypeCons

-- | Associates the name of a Haskell type variable with the corresponding Coq
--   identifier in the given environment.
--
--   If a type variable with the same name exists, the entry is overwritten.
defineTypeVar :: HS.Name -> G.Qualid -> Environment -> Environment
defineTypeVar name ident env =
  env { definedTypeVars = Map.insert name ident (definedTypeVars env) }

-- | Looks up the Coq identifier for a Haskell type variable with the given
--   name in the provided environment.
--
--   Returns @Nothing@ if there is no such type variable.
lookupTypeVar :: HS.Name -> Environment -> Maybe G.Qualid
lookupTypeVar name = Map.lookup name . definedTypeVars

-- | Associates the name of a Haskell data constructor with the corresponding
--   Coq identifiers for the constructor and smart constructor in the given
--   environment.
--
--   If a constructor with the same name exists, the entry is overwritten.
defineCon
  :: HS.Name  -- ^ The Haskell name of the constructor.
  -> Int      -- ^ The number of expected arguments.
  -> G.Qualid -- ^ The Coq identifier for the data constructor.
  -> G.Qualid -- ^ The Coq identifier for the smart constructor.
  -> Environment
  -> Environment
defineCon name arity ident smartIdent env = env
  { definedCons      = Map.insert name ident (definedCons env)
  , definedSmartCons = Map.insert name smartIdent (definedSmartCons env)
  , conArities       = Map.insert name arity (conArities env)
  }

-- | Looks up the Coq identifier for the regular constructor of the Haskell
--   data constructor with the given name in the provided environment.
--
--   Returns @Nothing@ if there is no such data constructor.
lookupCon :: HS.Name -> Environment -> Maybe G.Qualid
lookupCon name = Map.lookup name . definedCons

-- | Looks up the Coq identifier for the smart constructor of the Haskell
--   data constructor with the given name in the provided environment.
--
--   Returns @Nothing@ if there is no such smart constructor.
lookupSmartCon :: HS.Name -> Environment -> Maybe G.Qualid
lookupSmartCon name = Map.lookup name . definedSmartCons

-- | Associates the name of a Haskell variable with the corresponding Coq
--   identifier in the given environment.
--
--   If a function or variable with the same name exists, the entry is
--   overwritten.
defineVar :: HS.Name -> G.Qualid -> Environment -> Environment
defineVar = flip defineFunc 0

-- | Associates the name of a Haskell function with the corresponding Coq
--   identifier in the given environment.
--
--   If a function or variable with the same name exists, the entry is
--   overwritten.
defineFunc :: HS.Name -> Int -> G.Qualid -> Environment -> Environment
defineFunc name arity ident env = env
  { definedVars = Map.insert name ident (definedVars env)
  , varArities  = Map.insert name arity (varArities env)
  }

-- | Looks up the Coq identifier for a Haskell function or variable with the
--   given name in the provided environment.
--
--   Returns @Nothing@ if there is no such function or variable.
lookupVar :: HS.Name -> Environment -> Maybe G.Qualid
lookupVar name = Map.lookup name . definedVars

-------------------------------------------------------------------------------
-- State monad                                                               --
-------------------------------------------------------------------------------

-- | Type synonym for the state monad used by the converter.
--
--   All converter functions usually require the current 'Environment'
--   to perform the conversion. This monad allows these functions to
--   pass the environment around implicitly.
--
--   Additionally the converter can report error messages and warnings to the
--   user if there is a problem while converting.
newtype Converter a = Converter
  { unwrapConverter :: StateT Environment Reporter a
  }
  deriving (Functor, Applicative, Monad, MonadState Environment)

-- | Runs the converter with the given initial environment and
--   returns the converter's result as well as the final environment.
runConverter :: Converter a -> Environment -> Reporter (a, Environment)
runConverter = runStateT . unwrapConverter

-- | Runs the converter with the given initial environment and
--   returns the converter's result.
evalConverter :: Converter a -> Environment -> Reporter a
evalConverter = evalStateT . unwrapConverter

-- | Runs the converter with the given initial environment and
--   returns the final environment.
execConverter :: Converter a -> Environment -> Reporter Environment
execConverter = execStateT . unwrapConverter

-------------------------------------------------------------------------------
-- Modifying environments                                                    --
-------------------------------------------------------------------------------

-- | Gets the current environment.
getEnv :: Converter Environment
getEnv = get

-- | Gets a specific component of the current environment using the given
--   function to extract the value from the environment.
inEnv :: (Environment -> a) -> Converter a
inEnv = gets

-- | Sets the current environment.
putEnv :: Environment -> Converter ()
putEnv = put

-- | Applies the given function to the environment.
modifyEnv :: (Environment -> Environment) -> Converter ()
modifyEnv = modify

-- | Runs the given converter and returns its result but discards all
--   modifications to the environment.
localEnv :: Converter a -> Converter a
localEnv converter = do
  env <- getEnv
  x   <- converter
  putEnv env
  return x

-------------------------------------------------------------------------------
-- Reporting in converter                                                    --
-------------------------------------------------------------------------------

-- | Promotes a reporter to a converter that produces the same result and
--   ignores the environment.
--
--   This type class instance allows 'report' and 'reportFatal' to be used
--   directly in @do@-blocks of the 'Converter' monad without explicitly
--   lifting reporters.
instance MonadReporter Converter where
  liftReporter = Converter . lift

-- | Internal errors (e.g. pattern matching failures in @do@-blocks) are
--   cause fatal error messages to be reported.
instance MonadFail Converter where
  fail = reportFatal . Message Nothing Internal
