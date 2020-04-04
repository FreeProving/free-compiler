-- | This module contains the name of the @Test.QuickCheck@ module as well
--   as the names of data types and operations from the @Test.QuickCheck@
--   module that are needed for code generation.
--
--   Since QuickCheck properties are translated using the same mechanisms
--   as regular functions and the QuickCheck module is imported from its
--   module interface file like every other module, we actually don't
--   have to know the contents of the QuickCheck module at all.

module FreeC.IR.Base.Test.QuickCheck where

import qualified FreeC.IR.Syntax.Name          as HS

-- | The name of the @Test.QuickCheck@ module.
modName :: HS.ModName
modName = "Test.QuickCheck"
