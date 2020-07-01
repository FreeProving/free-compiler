-- | This module contains utility functions for tests that have to parse
--   the intermediate representation.
--
--   There is one general function that works with any AST node that has a
--   'Parseable' instance as well as a specialized function for each AST
--   node with a 'Parseable' instance. The specialized functions are mainly
--   to be used for documentation purposes and to avoid expression type
--   signatures in places where Haskell cannot infer the type of the node
--   to parse.
--
--   There are two versions of the parsing functions. The functions with
--   @parseTest@ prefix parse the input string and report errors to an
--   arbitrary 'MonadReporter'. The functions with @expectParseTest@ prefix,
--   on the other hand, set the expectation that parsing is successful.
--   If there is a parse error, an assertion failure will cause the test
--   to fail immediately. The latter kind of functions is supposed to be
--   used for setup actions. The example below illustrates how to use
--   these functions.
--
--   > it "..." $ do
--   >   expr <- expectParseTestExpr "..."
--   >   foo expr `shouldReturn` something
--
--   This pattern is especially important when testing for failures. In the
--   following example, we cannot distinguish whether @foo@ failed or we have
--   a typo in our test expression.
--
--   > it "..." $ shouldFail $ do
--   >   expr <- parseTestExpr "..."
--   >   foo expr
--
--   Thus, we should rewrite such tests as follows (if possible).
--
--   > it "..." $ do
--   >   expr <- expectParseTestExpr "..."
--   >   shouldFail (foo expr)


module FreeC.Test.Parser
  ( -- * Within Reporters
    parseTestIR
  , parseTestName
  , parseTestQName
  , parseTestType
  , parseTestTypeSchema
  , parseTestTypeDecl
  , parseTestTypeSig
  , parseTestExpr
  , parseTestFuncDecl
  , parseTestImportDecl
  , parseTestModule
    -- * Within Expectations
  , expectParseTestIR
  , expectParseTestName
  , expectParseTestQName
  , expectParseTestType
  , expectParseTestTypeSchema
  , expectParseTestTypeDecl
  , expectParseTestTypeSig
  , expectParseTestExpr
  , expectParseTestFuncDecl
  , expectParseTestImportDecl
  , expectParseTestModule
    -- * Parsing Dependency Components
  , parseTestComponent
  , expectParseTestComponent
  )
where

import           Control.Monad.IO.Class         ( MonadIO(..) )
import           Control.Monad.Fail             ( MonadFail )
import           Test.HUnit.Base                ( assertFailure )

import           FreeC.IR.DependencyGraph
import           FreeC.IR.SrcSpan
import           FreeC.Frontend.IR.Parser
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Reporter
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Within Reporters                                                          --
-------------------------------------------------------------------------------

-- | Parses an IR node of type @a@ for testing purposes.
parseTestIR :: (MonadReporter r, Parseable a) => String -> r a
parseTestIR = parseIR . mkSrcFile "<test-input>"

-- | Parses an IR name for testing purposes.
parseTestName :: MonadReporter r => String -> r IR.Name
parseTestName = parseTestIR

-- | Parses a qualifiable IR name for testing purposes.
parseTestQName :: MonadReporter r => String -> r IR.QName
parseTestQName = parseTestIR

-- | Parses an IR type expression for testing purposes.
parseTestType :: MonadReporter r => String -> r IR.Type
parseTestType = parseTestIR

-- | Parses an IR type schema for testing purposes.
parseTestTypeSchema :: MonadReporter r => String -> r IR.TypeSchema
parseTestTypeSchema = parseTestIR

-- | Parses an IR type declaration for testing purposes.
parseTestTypeDecl :: MonadReporter r => String -> r IR.TypeDecl
parseTestTypeDecl = parseTestIR

-- | Parses an IR type declaration for testing purposes.
parseTestTypeSig :: MonadReporter r => String -> r IR.TypeSig
parseTestTypeSig = parseTestIR

-- | Parses an IR expression for testing purposes.
parseTestExpr :: MonadReporter r => String -> r IR.Expr
parseTestExpr = parseTestIR

-- | Parses an IR function declaration for testing purposes.
parseTestFuncDecl :: MonadReporter r => String -> r IR.FuncDecl
parseTestFuncDecl = parseTestIR

-- | Parses an IR import declaration for testing purposes.
parseTestImportDecl :: MonadReporter r => String -> r IR.ImportDecl
parseTestImportDecl = parseTestIR

-- | Parses an IR module for testing purposes.
parseTestModule :: MonadReporter r => [String] -> r IR.Module
parseTestModule = parseTestIR . unlines

-------------------------------------------------------------------------------
-- Within Expectations                                                       --
-------------------------------------------------------------------------------

-- | Parses an IR node of type @a@ for testing purposes and sets the
--   expectation that parsing is successful.
--
--   The first argument is a textual description of the type of node to parse.
expectParseTestIR :: (MonadIO m, Parseable a) => String -> String -> m a
expectParseTestIR nodeType input = do
  let (mx, ms) = runReporter (parseTestIR input)
  case mx of
    Just x -> return x
    Nothing ->
      liftIO
        $  assertFailure
        $  "Could not parse test "
        ++ nodeType
        ++ ".\nThe following "
        ++ show (length ms)
        ++ " messages were reported:\n"
        ++ showPretty ms

-- | Parses an IR name for testing purposes and sets the
--   expectation that parsing is successful.
expectParseTestName :: MonadIO m => String -> m IR.Name
expectParseTestName = expectParseTestIR "name"

-- | Parses a qualifiable IR name for testing purposes and sets the
--   expectation that parsing is successful.
expectParseTestQName :: MonadIO m => String -> m IR.QName
expectParseTestQName = expectParseTestIR "qualifiable name"

-- | Parses an IR type expression for testing purposes and sets the
--   expectation that parsing is successful.
expectParseTestType :: MonadIO m => String -> m IR.Type
expectParseTestType = expectParseTestIR "type expression"

-- | Parses an IR type schema for testing purposes and sets the
--   expectation that parsing is successful.
expectParseTestTypeSchema :: MonadIO m => String -> m IR.TypeSchema
expectParseTestTypeSchema = expectParseTestIR "type schema"

-- | Parses an IR type declaration for testing purposes and sets the
--   expectation that parsing is successful.
expectParseTestTypeDecl :: MonadIO m => String -> m IR.TypeDecl
expectParseTestTypeDecl = expectParseTestIR "type declaration"

-- | Parses an IR type declaration for testing purposes and sets the
--   expectation that parsing is successful.
expectParseTestTypeSig :: MonadIO m => String -> m IR.TypeSig
expectParseTestTypeSig = expectParseTestIR "type signature"

-- | Parses an IR expression for testing purposes and sets the
--   expectation that parsing is successful.
expectParseTestExpr :: MonadIO m => String -> m IR.Expr
expectParseTestExpr = expectParseTestIR "expression"

-- | Parses an IR function declaration for testing purposes and sets the
--   expectation that parsing is successful.
expectParseTestFuncDecl :: MonadIO m => String -> m IR.FuncDecl
expectParseTestFuncDecl = expectParseTestIR "function declaration"

-- | Parses an IR import declaration for testing purposes and sets the
--   expectation that parsing is successful.
expectParseTestImportDecl :: MonadIO m => String -> m IR.ImportDecl
expectParseTestImportDecl = expectParseTestIR "import"

-- | Parses an IR module for testing purposes and sets the
--   expectation that parsing is successful.
expectParseTestModule :: MonadIO m => [String] -> m IR.Module
expectParseTestModule = expectParseTestIR "module" . unlines

-------------------------------------------------------------------------------
-- Parsing Dependency Components                                             --
-------------------------------------------------------------------------------

-- | Parses the declarations in the given dependency component.
parseTestComponent
  :: (MonadFail r, MonadReporter r, Parseable decl)
  => DependencyComponent String
  -> r (DependencyComponent decl)
parseTestComponent = mapComponentM (mapM parseTestIR)

-- | Parses the declarations in the given dependency component and sets the
--   expectation that parsing is successful.
expectParseTestComponent
  :: (MonadFail m, MonadIO m, Parseable decl)
  => DependencyComponent String
  -> m (DependencyComponent decl)
expectParseTestComponent =
  mapComponentM (mapM (expectParseTestIR "dependency component"))
