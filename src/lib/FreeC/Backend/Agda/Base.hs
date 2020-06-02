-- | This module contains the Agda identifiers of types, constructors and
--   functions defined in the Base library that accompanies the compiler.

module FreeC.Backend.Agda.Base where

-- We always import this module qualified, therefore clashing with the Prelude
-- isn't a problem.
import           Prelude                 hiding ( pure )

import qualified FreeC.Backend.Agda.Syntax     as Agda

-------------------------------------------------------------------------------
-- Base library import                                                       --
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

shapes :: Agda.Name
shapes = Agda.name "S"

positions :: Agda.Name
positions = Agda.name "P"

-------------------------------------------------------------------------------
-- Reserved identifiers                                                      --
-------------------------------------------------------------------------------

-- | All Agda identifiers that are reserved for the Base library.
--
--   This does only include identifiers without corresponding Haskell name.
reservedIdents :: [Agda.Name]
reservedIdents = [free, pureConName, impureConName, shapes, positions]
