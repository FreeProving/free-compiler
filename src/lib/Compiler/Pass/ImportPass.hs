-- | This module contains a compiler pass that adds all entries from imported
--   modules to the environment.
--
--   = Example
--
--   When a module @A@ that exports a data type @Foo@
--
--   @
--   module A where
--
--   data Foo = Foo
--   @
--
--   is imported by a module @B@
--
--   @
--   module B where
--
--   import A
--
--   type Bar a = Foo -> a
--   @
--
--   then an entry for @Foo@ is added to the environment under its original
--   name @A.Foo@. The resolver pass will make sure that the reference to @Foo@
--   in the declaration of @Bar@ is resolved to @A.Foo@. Thus, the entry for
--   @Foo@ can be looked up in the translation of @B@.
--
--   When a module @C@ imports @B@
--
--   @
--   module C where
--
--   import B
--
--   baz :: Bar ()
--   baz x = ()
--   @
--
--   both @A.Foo@ and @B.Bar@ are added to the environment of @C@ since all
--   entries imported by @B@ are part of the @B@'s module interface.
--   In the example above this is needed among others during type inference.
--   To infer the type of @x@ the type synonym @Bar@ needs to be expanded.
--   The type of @x@ is @A.Foo@. Thus, the corresponding entry must be visible.
--   The resolver pass will make sure that @C@ does not directly refer to the
--   hidden entries of @B@'s module interface.
--
--   = Specification
--
--   == Preconditions
--
--   Module interfaces for all imported modules must be available.
--
--   == Translation
--
--   No modifications are made to the AST. All entries from module interfaces
--   of imported modules are added to the environment. This includes entries
--   that are not exported by the imported module.
--
--   == Postconditions
--
--   All external entries that could be referenced (directly or indirectly)
--   by the module are in the environment.
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
import qualified Compiler.IR.Syntax            as HS
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pass

-- | Compiler pass that adds entries imported by the given module to the
--   environment.
importPass :: Pass HS.Module
importPass ast = do
  mapM_ importModule (HS.modImports ast)
  return ast

-- | Adds the entries of the module interface imported by the given import
--   declaration to the environment.
--
--   Reports a fatal error when there is no such module.
importModule :: HS.ImportDecl -> Converter ()
importModule (HS.ImportDecl srcSpan modName) = do
  maybeIface <- inEnv $ lookupAvailableModule modName
  case maybeIface of
    Just iface -> modifyEnv $ importInterface iface
    Nothing ->
      reportFatal
        $  Message srcSpan Error
        $  "Could not find module '"
        ++ modName
        ++ "'"
