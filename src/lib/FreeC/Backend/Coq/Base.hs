-- | This module contains the Coq identifiers of types, constructors and
--   functions defined in the Base library that accompanies the compiler.
module FreeC.Backend.Coq.Base
  ( -- * Base Library Import
    imports
  , baseLibName
  , generatedLibName
    -- * Free Monad
  , free
  , shape
  , pos
  , freePureCon
  , freeImpureCon
  , freeBind
  , freeArgs
  , shape
  , shapeIdent
  , pos
  , posIdent
    -- * Partiality
  , partial
  , partialArg
  , partialUndefined
  , partialError
    -- * Sharing
  , injectable
  , injectableBinder
  , strategy
  , strategyArg
  , shareableArgs
  , shareableArgsBinder
  , implicitArg
  , share
    -- * Effect Selection
  , selectExplicitArgs
  , selectImplicitArgs
  , selectTypedImplicitArgs
  , selectBinders
  , selectTypedBinders
    -- * Literal Scopes
  , integerScope
  , stringScope
    -- * Reserved Identifiers
  , reservedIdents
  ) where

import qualified FreeC.Backend.Coq.Syntax as Coq
import           FreeC.LiftedIR.Effect

-------------------------------------------------------------------------------
-- Base Library Import                                                       --
-------------------------------------------------------------------------------
-- | Import sentence for the @Free@ module from the Base Coq library.
imports :: Coq.Sentence
imports = Coq.requireImportFrom baseLibName [Coq.ident "Free"]

-- | The name of the Base Coq library.
baseLibName :: Coq.ModuleIdent
baseLibName = Coq.ident "Base"

-- | The name of the Coq library where generated Coq files are placed.
generatedLibName :: Coq.ModuleIdent
generatedLibName = Coq.ident "Generated"

-------------------------------------------------------------------------------
-- Free Monad                                                                --
-------------------------------------------------------------------------------
-- | The Coq identifier for the @Free@ monad.
free :: Coq.Qualid
free = Coq.bare "Free"

-- | The Coq identifier for the @Shape@ argument of the @Free@ monad.
shape :: Coq.Qualid
shape = Coq.Bare shapeIdent

-- | Like 'shape' but not wrapped in a 'Coq.Bare' constructor.
shapeIdent :: Coq.Ident
shapeIdent = Coq.ident "Shape"

-- | The Coq identifier for the @Pos@ argument of the @Free@ monad.
pos :: Coq.Qualid
pos = Coq.Bare posIdent

-- | Like 'pos' but not wrapped in a 'Coq.Bare' constructor.
posIdent :: Coq.Ident
posIdent = Coq.ident "Pos"

-- | The Coq identifier for the @pure@ constructor of the @Free@ monad.
freePureCon :: Coq.Qualid
freePureCon = Coq.bare "pure"

-- | The Coq identifier for the @impure@ constructor of the @Free@ monad.
freeImpureCon :: Coq.Qualid
freeImpureCon = Coq.bare "impure"

-- | The Coq identifier for the @>>=@ operator of the @Free@ monad.
freeBind :: Coq.Qualid
freeBind = Coq.bare "op_>>=__"

-- | The names and types of the parameters that must be passed to the @Free@
--   monad. These parameters are added automatically to every defined type and
--   function.
freeArgs :: [(Coq.Qualid, Coq.Term)]
freeArgs = [ (shape, Coq.Sort Coq.Type)
           , (pos, Coq.Arrow (Coq.Qualid shape) (Coq.Sort Coq.Type))
           ]

-------------------------------------------------------------------------------
-- Partiality                                                                --
-------------------------------------------------------------------------------
-- | The Coq identifier for the @Partial@ type class.
partial :: Coq.Qualid
partial = Coq.bare "Partial"

-- | The Coq identifier for the argument of the @Partial@ type class.
partialArg :: Coq.Qualid
partialArg = Coq.bare "P"

-- | The Coq binder for the @Partial@ type class.
partialBinder :: Coq.Binder
partialBinder = Coq.typedBinder' Coq.Ungeneralizable Coq.Explicit partialArg
  $ Coq.app (Coq.Qualid partial) [Coq.Qualid shape, Coq.Qualid pos]

-- | The identifier for the error term @undefined@.
partialUndefined :: Coq.Qualid
partialUndefined = Coq.bare "undefined"

-- | The identifier for the error term @error@.
partialError :: Coq.Qualid
partialError = Coq.bare "error"

-------------------------------------------------------------------------------
-- Sharing                                                                   --
-------------------------------------------------------------------------------
-- | The Coq identifier for the @Share@ module.
shareModuleIdent :: Coq.Ident
shareModuleIdent = Coq.ident "Share"

-- | The Coq identifier for the @Injectable@ type class.
injectable :: Coq.Qualid
injectable = Coq.bare "Injectable"

-- | The Coq binder for the @Injectable@ type class.
injectableBinder :: Coq.Binder
injectableBinder = Coq.Generalized Coq.Implicit
  $ Coq.app (Coq.Qualid injectable)
  $ map Coq.Qualid [ Coq.Qualified shareModuleIdent shapeIdent
                   , Coq.Qualified shareModuleIdent posIdent
                   , shape
                   , pos
                   ]

-- | The Coq identifier for the @Strategy@ type class.
strategy :: Coq.Qualid
strategy = Coq.bare "Strategy"

-- | The Coq identifier for the argument of the @Strategy@ type class.
strategyArg :: Coq.Qualid
strategyArg = Coq.bare "S"

-- | The Coq binder for the @Strategy@ type class.
strategyBinder :: Coq.Binder
strategyBinder = Coq.typedBinder' Coq.Ungeneralizable Coq.Explicit strategyArg
  $ Coq.app (Coq.Qualid strategy) [Coq.Qualid shape, Coq.Qualid pos]

-- | The Coq binder for the @ShareableArgs@ type class.
shareableArgs :: Coq.Qualid
shareableArgs = Coq.bare "ShareableArgs"

-- | The Coq binder for the @ShareableArgs@ type class with the type variable
--   with the given name.
shareableArgsBinder :: Coq.Qualid -> Coq.Binder
shareableArgsBinder typeArg = Coq.Generalized Coq.Implicit
  $ Coq.app (Coq.Qualid shareableArgs)
  $ map Coq.Qualid [shape, pos, typeArg]

-- | The Coq identifier for an implicit argument.
implicitArg :: Coq.Term
implicitArg = Coq.Underscore

-- | The Coq Identifier for the @share@ operator.
share :: Coq.Qualid
share = Coq.bare "share"

-------------------------------------------------------------------------------
-- Effect selection                                                          --
-------------------------------------------------------------------------------
-- | Selects the correct explicit function arguments for the given effect.
selectExplicitArgs :: Effect -> [Coq.Term]
selectExplicitArgs Partiality = [Coq.Qualid partialArg]
selectExplicitArgs Sharing    = [Coq.Qualid strategyArg]

-- | Selects the correct implicit function arguments for the given effect.
selectImplicitArgs :: Effect -> [Coq.Term]
selectImplicitArgs Partiality = []
selectImplicitArgs Sharing    = [implicitArg]

-- | Like 'selectImplicitArgs' but the arguments have to be inserted after
--   the type arguments the specified number of times.
selectTypedImplicitArgs :: Effect -> Int -> [Coq.Term]
selectTypedImplicitArgs Partiality = const []
selectTypedImplicitArgs Sharing    = flip replicate implicitArg

-- | Selects the correct binder for the given effect.
selectBinders :: Effect -> [Coq.Binder]
selectBinders Partiality = [partialBinder]
selectBinders Sharing    = [injectableBinder, strategyBinder]

-- | Like 'selectBinders' but the binders are dependent on the type variables
--   with the given names.
selectTypedBinders :: Effect -> [Coq.Qualid] -> [Coq.Binder]
selectTypedBinders Partiality = const []
selectTypedBinders Sharing    = map shareableArgsBinder

-------------------------------------------------------------------------------
-- Literal Scopes                                                            --
-------------------------------------------------------------------------------
-- | The scope of integer literals.
integerScope :: Coq.Ident
integerScope = Coq.ident "Z"

-- | The scope of string literals used in @error@ terms.
stringScope :: Coq.Ident
stringScope = Coq.ident "string"

-------------------------------------------------------------------------------
-- Reserved Identifiers                                                      --
-------------------------------------------------------------------------------
-- | All Coq identifiers that are reserved for the Base library.
--
--   This does only include identifiers without corresponding Haskell name.
reservedIdents :: [Coq.Qualid]
reservedIdents
  = [ -- Free monad
      free
    , freePureCon
    , freeImpureCon
      -- Partiality
    , partial
    , partialArg
    , partialUndefined
    , partialError
      -- Sharing
    , injectable
    , strategy
    , strategyArg
    , shareableArgs
    , share
    ]
  ++ map fst freeArgs
