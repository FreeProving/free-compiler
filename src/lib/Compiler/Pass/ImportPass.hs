-- | This module contains a compiler pass that brings the entries of
--   exported by imported modules into scope. The @Prelude@ is imported
--   implicitly.
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
--   {- ... -}
--   @
--
--   it is added to the import list
--
--   @
--   module Queue where
--
--   import Prelude
--   import Test.QuickCheck
--
--   type Queue a = ([a], [a])
--   {- ... -}
--   @
--
--   In the example above all functions, data types and constructors
--   exported by the @Prelude@ and @Test.QuickCheck@ modules are added
--   to the environment by their qualified and unqualified name. For
--   instance, the function @negate@ from the @Prelude@ module is in
--   scope as @negate@ and @Prelude.negate@ after this pass.
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
--   For each import of the form @import M@ where @M@ is the name of an
--   module for which a 'ModuleInterface' is available, all entries from
--   the module interface are added to the environment. The entries are
--   associated with both their unqualified and qualified names, i.e.,
--   if the module exports an entry @x@, then both @x@ and @M.x@ are in
--   scope.
--
--   == Postconditions
--
--   All entries exported by the imported modules are in scope and there
--   is an explicit import for the @Prelude@ module.
--
--   == Error cases
--
--   * A fatal error is reported if there is an import for a module @M@ but
--     there is no such module interface available.

module Compiler.Pass.ImportPass
  ( importPass
  )
where

import           Compiler.Environment
import           Compiler.Environment.Importer
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter

-- | Brings the entries imported by the given module into scope.
importPass :: HS.Module -> Converter HS.Module
importPass ast = do
  let imports' = addImplicitPreludeImport (HS.modImports ast)
  mapM_ importModule imports'
  return ast { HS.modImports = imports' }

-- | Adds an import for the @Prelude@ module to the given list of imports if
--   there is no explicit import for the @Prelude@ already.
addImplicitPreludeImport :: [HS.ImportDecl] -> [HS.ImportDecl]
addImplicitPreludeImport imports | importsPrelude = imports
                                 | otherwise      = preludeImport : imports
 where
  -- | Whether there is an explicit import for the @Prelude@ module.
  importsPrelude :: Bool
  importsPrelude = HS.preludeModuleName `elem` map HS.importName imports

  -- | An explicit import for the @Prelude@ module.
  preludeImport :: HS.ImportDecl
  preludeImport = HS.ImportDecl NoSrcSpan HS.preludeModuleName

-- | Adds the entries of the module interface imported by the given import
--   declaration to the environment.
--
--   Reports a fatal error when there is no such module.
importModule :: HS.ImportDecl -> Converter ()
importModule (HS.ImportDecl srcSpan modName) = do
  maybeIface <- inEnv $ lookupAvailableModule modName
  case maybeIface of
    Just iface -> do
      modifyEnv $ importInterface iface
      modifyEnv $ importInterfaceAs modName iface
    Nothing ->
      reportFatal
        $  Message srcSpan Error
        $  "Could not find module '"
        ++ modName
        ++ "'"
