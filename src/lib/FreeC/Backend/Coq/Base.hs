-- | This module contains the Coq identifiers of types, constructors and
--   functions defined in the Base library that accompanies the compiler.

module FreeC.Backend.Coq.Base where

import qualified FreeC.Backend.Coq.Syntax      as Coq

-------------------------------------------------------------------------------
-- Base library import                                                       --
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
-- Free monad                                                                --
-------------------------------------------------------------------------------

-- | The Coq identifier for the @Free@ monad.
free :: Coq.Qualid
free = Coq.bare "Free"

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
freeArgs =
  [ (Coq.bare "Shape", Coq.Sort Coq.Type)
  , ( Coq.bare "Pos"
    , Coq.Arrow (Coq.Qualid (Coq.bare "Shape")) (Coq.Sort Coq.Type)
    )
  ]

-------------------------------------------------------------------------------
-- Partiality                                                                --
-------------------------------------------------------------------------------

-- | The name of the type class @Partial@
partial :: Coq.Qualid
partial = Coq.bare "Partial"

-- | The name and type of the @Partial@ instance that must be passed to
--   partial functions.
partialArg :: (Coq.Qualid, Coq.Term)
partialArg =
  ( Coq.bare "P"
  , Coq.app (Coq.Qualid (Coq.bare "Partial"))
            [Coq.Qualid (Coq.bare "Shape"), Coq.Qualid (Coq.bare "Pos")]
  )

-- | The identifier for the error term @undefined@.
partialUndefined :: Coq.Qualid
partialUndefined = Coq.bare "undefined"

-- | The identifier for the error term @error@.
partialError :: Coq.Qualid
partialError = Coq.bare "error"

-------------------------------------------------------------------------------
-- Literal scopes                                                            --
-------------------------------------------------------------------------------

-- | The scope of integer literals.
integerScope :: Coq.Ident
integerScope = Coq.ident "Z"

-- | The scope of string literals used in @error@ terms.
stringScope :: Coq.Ident
stringScope = Coq.ident "string"

-------------------------------------------------------------------------------
-- Reserved identifiers                                                      --
-------------------------------------------------------------------------------

-- | All Coq identifiers that are reserved for the Base library.
--
--   This does only include identifiers without corresponding Haskell name.
reservedIdents :: [Coq.Qualid]
reservedIdents =
  [ -- Free monad
    free
    , freePureCon
    , freeImpureCon
    -- Partiality
    , partial
    , partialUndefined
    , partialError
    ]
    ++ map fst (partialArg : freeArgs)
