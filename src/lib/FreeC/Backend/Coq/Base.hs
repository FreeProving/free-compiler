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
  , idShape
  , idPos
  , freePureCon
  , freeImpureCon
  , freeBind
  , freeArgs
  , shapeIdent
  , posIdent
  , forFree
    -- * Partiality
  , partial
  , partialArg
  , partialUndefined
  , partialError
    -- * Tracing
  , traceable
  , traceableArg
  , trace
    -- * Modules
  , qualifiedSmartConstructorModule
    -- * Sharing
  , strategy
  , strategyArg
  , strategyBinder
  , shareableArgs
  , shareableArgsBinder
  , shareArgs
  , normalform
  , normalformBinder
  , nf'
  , nf
  , nType
  , implicitArg
  , share
  , shareWith
    -- * Effect Selection
  , selectExplicitArgs
  , selectImplicitArgs
  , selectTypedImplicitArgs
  , selectBinders
  , selectTypedBinders
    -- * Literal Scopes
  , integerScope
  , stringScope
    -- * Tactics
  , proveInd
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

-- | The Coq identifier for the @Identity@ shape.
idShape :: Coq.Qualid
idShape = Coq.Qualified (Coq.ident "Identity") shapeIdent

-- | The Coq identifier for the @Identity@ position function.
idPos :: Coq.Qualid
idPos = Coq.Qualified (Coq.ident "Identity") posIdent

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

-- | The Coq identifier for the @ForFree@ property.
forFree :: Coq.Qualid
forFree = Coq.bare "ForFree"

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
-- Tracing                                                                   --
-------------------------------------------------------------------------------
-- | The Coq identifier for the @Traceable@ type class.
traceable :: Coq.Qualid
traceable = Coq.bare "Traceable"

-- | The Coq identifier for the argument of the @Traceable@ type class.
traceableArg :: Coq.Qualid
traceableArg = Coq.bare "T"

-- | The Coq binder for the @Traceable@ type class.
tracableBinder :: Coq.Binder
tracableBinder = Coq.typedBinder' Coq.Ungeneralizable Coq.Explicit traceableArg
  $ Coq.app (Coq.Qualid traceable) [Coq.Qualid shape, Coq.Qualid pos]

-- | The identifier for the effect @trace@.
trace :: Coq.Qualid
trace = Coq.bare "trace"

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------
-- | The name of the local module, where qualified smart constructor notations
--   are defined.
qualifiedSmartConstructorModule :: Coq.Ident
qualifiedSmartConstructorModule = Coq.ident "QualifiedSmartConstructorModule"

-------------------------------------------------------------------------------
-- Sharing                                                                   --
-------------------------------------------------------------------------------
-- | The Coq identifier for the @Strategy@ type class.
strategy :: Coq.Qualid
strategy = Coq.bare "Strategy"

-- | The Coq identifier for the argument of the @Strategy@ type class.
strategyArg :: Coq.Qualid
strategyArg = Coq.bare "S"

strategyBinder :: Coq.Binder
strategyBinder = Coq.typedBinder' Coq.Ungeneralizable Coq.Explicit strategyArg
  (Coq.app (Coq.Qualid strategy) [Coq.Qualid shape, Coq.Qualid pos])

-- | The Coq identifier for the @ShareableArgs@ type class.
shareableArgs :: Coq.Qualid
shareableArgs = Coq.bare "ShareableArgs"

-- | The Coq binder for the @ShareableArgs@ type class with the type variable
--   with the given name.
shareableArgsBinder :: Coq.Qualid -> Coq.Binder
shareableArgsBinder typeArg = Coq.Generalized Coq.Implicit
  $ Coq.app (Coq.Qualid shareableArgs)
  $ map Coq.Qualid [shape, pos, typeArg]

-- | The Coq identifier of the @ShareableArgs@ class function.
shareArgs :: Coq.Qualid
shareArgs = Coq.bare "shareArgs"

-- | The Coq identifier for an implicit argument.
implicitArg :: Coq.Term
implicitArg = Coq.Underscore

-- | The Coq identifier for the @share@ operator.
share :: Coq.Qualid
share = Coq.bare "share"

-- | The Coq identifier for the @shareWith@ operator.
shareWith :: Coq.Qualid
shareWith = Coq.bare "shareWith"

-------------------------------------------------------------------------------
-- Handling                                                                  --
-------------------------------------------------------------------------------
-- | The Coq identifier for the @Normalform@ type class.
normalform :: Coq.Qualid
normalform = Coq.bare "Normalform"

-- | The Coq binder for the @Normalform@ type class with the source and target
--   type variable with the given names.
normalformBinder :: Coq.Qualid -> Coq.Binder
normalformBinder a = Coq.Generalized Coq.Implicit
  $ Coq.app (Coq.Qualid normalform)
  $ map Coq.Qualid [shape, pos, a]

-- | The Coq identifier of the @Normalform@ class function.
nf' :: Coq.Qualid
nf' = Coq.bare "nf'"

-- | The Coq identifier of the function @nf@.
nf :: Coq.Qualid
nf = Coq.bare "nf"

-- | The Coq identifier for a normalized type.
nType :: Coq.Qualid
nType = Coq.bare "nType"

-------------------------------------------------------------------------------
-- Effect selection                                                          --
-------------------------------------------------------------------------------
-- | Selects the correct explicit function arguments for the given effect.
selectExplicitArgs :: Effect -> [Coq.Term]
selectExplicitArgs Partiality = [Coq.Qualid partialArg]
selectExplicitArgs Sharing    = [Coq.Qualid strategyArg]
selectExplicitArgs Tracing    = [Coq.Qualid traceableArg]
selectExplicitArgs Normalform = []

-- | Selects the correct implicit function arguments for the given effect.
selectImplicitArgs :: Effect -> [Coq.Term]
selectImplicitArgs Partiality = []
selectImplicitArgs Sharing    = []
selectImplicitArgs Tracing    = []
selectImplicitArgs Normalform = []

-- | Like 'selectImplicitArgs' but the arguments have to be inserted after
--   the type arguments the specified number of times.
selectTypedImplicitArgs :: Effect -> Int -> [Coq.Term]
selectTypedImplicitArgs Partiality = const []
selectTypedImplicitArgs Sharing    = flip replicate implicitArg
selectTypedImplicitArgs Tracing    = const []
selectTypedImplicitArgs Normalform = flip replicate implicitArg

-- | Selects the correct binder for the given effect.
selectBinders :: Effect -> [Coq.Binder]
selectBinders Partiality = [partialBinder]
selectBinders Sharing    = [strategyBinder]
selectBinders Tracing    = [tracableBinder]
selectBinders Normalform = []

-- | Like 'selectBinders' but the binders are dependent on the type variables
--   with the given names.
selectTypedBinders :: Effect -> [Coq.Qualid] -> [Coq.Binder]
selectTypedBinders Partiality = const []
selectTypedBinders Sharing    = map shareableArgsBinder
selectTypedBinders Tracing    = const []
selectTypedBinders Normalform = map normalformBinder

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
-- Tactics                                                                   --
-------------------------------------------------------------------------------
-- | The tactic that is needed to prove induction schemes.
proveInd :: Coq.Qualid
proveInd = Coq.bare "prove_ind"

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
    , forFree
      -- Partiality
    , partial
    , partialArg
    , partialUndefined
    , partialError
      -- Tracing
    , traceable
    , traceableArg
    , trace
      -- Notations
    , Coq.Bare qualifiedSmartConstructorModule
      -- Sharing
    , strategy
    , strategyArg
    , shareableArgs
    , shareArgs
    , normalform
    , nf'
    , nf
    , nType
    , share
    , shareWith
    ]
  ++ map fst freeArgs
