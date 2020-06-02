-- | This module contains the Agda identifiers of types, constructors and
--   functions defined in the Base library that accompanies the compiler.

module FreeC.Backend.Agda.Base
  ( -- * Library imports
    baseLibName
  , generatedLibName
  , imports
    -- * Free Monad
  , free
  , pure
  , impure
  , shape
  , position
    -- * reserved identifiers
  , reservedIdents
  )
where

-- We always import this module qualified, therefore clashing with the Prelude
-- isn't a problem.
import           Prelude                 hiding ( pure )

import qualified FreeC.Backend.Agda.Syntax     as Agda

-------------------------------------------------------------------------------
-- Library imports                                                           --
-------------------------------------------------------------------------------

-- | The name of the Agda Base library.
baseLibName :: Agda.Name
baseLibName = Agda.name "Base"

-- | The name of the Agda library where generated Agda files are placed.
generatedLibName :: Agda.Name
generatedLibName = Agda.name "Generated"

-- | Import declaration for the @Free@ module from the Base Agda library.
imports :: Agda.Declaration
imports = Agda.simpleImport $ Agda.qname [baseLibName] $ Agda.name "Free"

-------------------------------------------------------------------------------
-- Free Monad                                                                --
-------------------------------------------------------------------------------

free :: Agda.Name
free = Agda.name "Free"

pureConName :: Agda.Name
pureConName = Agda.name "pure"

pure :: Agda.Expr -> Agda.Expr
pure = Agda.app $ Agda.Ident $ Agda.qname [Agda.name "Free"] pureConName

impureConName :: Agda.Name
impureConName = Agda.name "impure"

impure :: Agda.Expr -> Agda.Expr
impure = Agda.app $ Agda.Ident $ Agda.qname [Agda.name "Free"] impureConName

shape :: Agda.Name
shape = Agda.name "S"

position :: Agda.Name
position = Agda.name "P"

-------------------------------------------------------------------------------
-- Reserved identifiers                                                      --
-------------------------------------------------------------------------------

-- | All Agda identifiers that are reserved for the Base library.
--
--   This does only include identifiers without corresponding Haskell name.
reservedIdents :: [Agda.Name]
reservedIdents = [free, pureConName, impureConName, shape, position]
