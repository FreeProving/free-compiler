-- | This module contains the Agda identifiers of types, constructors and
--   functions defined in the Base library that accompanies the compiler.
module FreeC.Backend.Agda.Base
  ( -- * Library Imports
    baseLibName
  , generatedLibName
  , imports
    -- * Free Monad
  , free
  , pure
  , shape
  , position
  , partial
    -- * Sized Types
  , size
  , up
    -- * Reserved Identifiers
  , reservedIdents
  ) where

-- We always import this module qualified, therefore clashing with the Prelude
-- isn't a problem.
import           Prelude                   hiding ( pure )

import qualified FreeC.Backend.Agda.Syntax as Agda

-------------------------------------------------------------------------------
-- Library Imports                                                           --
-------------------------------------------------------------------------------
-- | The name of the Agda Base library.
baseLibName :: Agda.Name
baseLibName = Agda.name "Base"

-- | The name of the Agda library where generated Agda files are placed.
generatedLibName :: Agda.Name
generatedLibName = Agda.name "Generated"

-- | Import declaration for the @Free@ and @partial@ modules from the Base Agda
--   base library.
imports :: [Agda.Declaration]
imports = map (Agda.simpleImport . Agda.qname [baseLibName] . Agda.name)
  ["Free", "Partial"]

-------------------------------------------------------------------------------
-- Free Monad                                                                --
-------------------------------------------------------------------------------
-- | Identifier for the @Free@ monad.
free :: Agda.Name
free = Agda.name "Free"

-- | Identifier for the @pure@ constructor of the @Free@ monad.
pure :: Agda.Name
pure = Agda.name "pure"

-- | Identifier for the @impure@ constructor of the @Free@ monad.
impure :: Agda.Name
impure = Agda.name "impure"

-- | Reserved name for the @Shape@ type variable.
shape :: Agda.Name
shape = Agda.name "Shape"

-- | Reserved name for the @Pos@ type variable.
position :: Agda.Name
position = Agda.name "Pos"

-- | Reserved name for the @Partial@ type class.
partial :: Agda.Name
partial = Agda.name "Partial"

-------------------------------------------------------------------------------
-- Sized Types                                                               --
-------------------------------------------------------------------------------
-- | The name of Agda's @Size@ data type.
--
--   > Size
size :: Agda.Name
size = Agda.name "Size"

-- | The Name of the Agda function for larger @Size@.
--
--   > ↑
up :: Agda.Name
up = Agda.name "\x2191"

-------------------------------------------------------------------------------
-- Reserved Identifiers                                                      --
-------------------------------------------------------------------------------
-- | All Agda identifiers that are reserved for the Base library.
--
--   This does only include identifiers without corresponding Haskell name.
reservedIdents :: [Agda.Name]
reservedIdents = [free, pure, impure, shape, position, size, up, partial]
