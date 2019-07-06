-- | This module contains the Coq identifiers of types, constructors and
--   functions defined in the Base library that accompanies the compiler.

module Compiler.Language.Coq.Base where

import qualified Data.Text                     as T
import qualified Language.Coq.Gallina          as G

-- | The Coq identifier for the @Free@ monad.
free :: String
free = "Free"

-- | The Coq identifier for the @pure@ constructor of the @Free@ monad.
freePureCon :: String
freePureCon = "pure"

-- | The Coq identifier for the @impure@ constructor of the @Free@ monad.
freeImpureCon :: String
freeImpureCon = "impure"

-- | The names and types of the parameters that must be passed to the @Free@
--   monad. These parameters are added automatically to every defined type and
--   function.
freeArgs :: [(String, G.Term)]
freeArgs =
  [ ("Shape", G.Sort G.Type)
  , ("Pos", G.Arrow (G.Qualid (bare "Shape")) (G.Sort G.Type))
  ]

-- | All Coq identifiers that are reserved for the Base library.
--
--   This does only include identifiers without corresponding Haskell name.
reservedIdents :: [String]
reservedIdents = [free, freePureCon, freeImpureCon] ++ map fst freeArgs

-- | Smart constructor for Coq identifiers.
--
--   TODO create module for Coq smart constructors.
bare :: String -> G.Qualid
bare = G.Bare . T.pack
