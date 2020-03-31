-- | This module contains a compiler pass that add an import declaration
--   for the @Prelude@ module to the imports of a module if it does not
--   import the @Prelude@ explicitly.
--
--   = Example
--
--   If a module does not have an explicit import of the @Prelude@ module
--
--   @
--   module Queue where
--
--   import Test.QuickCheck
--
--   type Queue a = ([a], [a])
--
--   {- ... -}
--   @
--
--   an import for the @Prelude@ module is added to the import list
--
--   @
--   module Queue where
--
--   import Prelude
--   import Test.QuickCheck
--
--   type Queue a = ([a], [a])
--
--   {- ... -}
--   @
--
--   = Specification
--
--   == Preconditions
--
--   There are no special requirements.
--
--   == Translation
--
--   If the module does not contain an import of the form @import Prelude@
--   it is added to the top of the import list.
--
--   == Postconditions
--
--   There is an explicit import for the @Prelude@ module.
module FreeC.Pass.ImplicitPreludePass
  ( implicitPreludePass
  )
where

import qualified FreeC.IR.Base.Prelude         as HS.Prelude
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax               as HS
import           FreeC.Pass

-- | A compiler pass that adds an import declaration for the @Prelude@ module
--   if there is no such import.
implicitPreludePass :: Pass HS.Module
implicitPreludePass ast =
  return ast { HS.modImports = addImplicitPreludeImport (HS.modImports ast) }

-- | Adds an import for the @Prelude@ module to the given list of imports if
--   there is no explicit import for the @Prelude@ already.
addImplicitPreludeImport :: [HS.ImportDecl] -> [HS.ImportDecl]
addImplicitPreludeImport imports | importsPrelude = imports
                                 | otherwise      = preludeImport : imports
 where
  -- | Whether there is an explicit import for the @Prelude@ module.
  importsPrelude :: Bool
  importsPrelude = HS.Prelude.modName `elem` map HS.importName imports

  -- | An explicit import for the @Prelude@ module.
  preludeImport :: HS.ImportDecl
  preludeImport = HS.ImportDecl NoSrcSpan HS.Prelude.modName
