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

pure :: Agda.Expr -> Agda.Expr
pure = Agda.app $ Agda.Ident $ Agda.qname [Agda.name "Free"] $ Agda.name "pure"

impure :: Agda.Expr -> Agda.Expr
impure =
  Agda.app $ Agda.Ident $ Agda.qname [Agda.name "Free"] $ Agda.name "impure"

shapes :: Agda.Name
shapes = Agda.name "S"

positions :: Agda.Name
positions = Agda.name "P"
