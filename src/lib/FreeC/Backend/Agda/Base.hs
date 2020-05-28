-- | This module contains the Agda identifiers of types, constructors and
--   functions defined in the Base library that accompanies the compiler.

module FreeC.Backend.Agda.Base where

import qualified FreeC.Backend.Agda.Syntax     as Agda

-------------------------------------------------------------------------------
-- Base library import                                                       --
-------------------------------------------------------------------------------

-- | Import declaration for the @Free@ module from the Base Agda library.
imports :: Agda.Declaration
imports = Agda.simpleImport $ Agda.qname' $ Agda.name "Free"


