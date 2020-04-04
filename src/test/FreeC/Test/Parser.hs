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
--   arbitrary 'MonadReporter'. The functions with @expectParseTest@ prefix
--   on the other hand set the expectation that parsing is successful.
--   If there is a parse error, an assertion failure will cause the test
--   to fail immediately. The latter kind of functions are supposed to be
--   used for setup actions. The example below illustrates how to use
--   these functions.
--
--   @
--   it "..." $ do
--     expr <- expectParseTestExpr "..."
--     foo expr `shouldReturn` something
--   @

module FreeC.Test.Parser where

import           Control.Monad.IO.Class         ( MonadIO(..) )
import           Test.HUnit.Base                ( assertFailure )

import           FreeC.IR.SrcSpan
import           FreeC.Frontend.IR.Parser
import qualified FreeC.IR.Syntax               as HS
import           FreeC.Monad.Reporter
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Within Reporters                                                          --
-------------------------------------------------------------------------------

-- | Parses an IR node of type @a@ for testing purposes.
parseTestIR :: (MonadReporter r, Parseable a) => String -> r a
parseTestIR = parseIR . mkSrcFile "<test-input>"

-- | Parses an IR name for testing purposes.
parseTestName :: MonadReporter r => String -> r HS.Name
parseTestName = parseTestIR

-- | Parses a qualifiable IR name for testing purposes.
parseTestQName :: MonadReporter r => String -> r HS.QName
parseTestQName = parseTestIR

-- | Parses an IR type expression for testing purposes.
parseTestType :: MonadReporter r => String -> r HS.Type
parseTestType = parseTestIR

-- | Parses an IR type schema for testing purposes.
parseTestTypeSchema :: MonadReporter r => String -> r HS.TypeSchema
parseTestTypeSchema = parseTestIR

-- | Parses an IR type declaration for testing purposes.
parseTestTypeDecl :: MonadReporter r => String -> r HS.TypeDecl
parseTestTypeDecl = parseTestIR

-- | Parses an IR type declaration for testing purposes.
parseTestTypeSig :: MonadReporter r => String -> r HS.TypeSig
parseTestTypeSig = parseTestIR

-- | Parses an IR expression for testing purposes.
parseTestExpr :: MonadReporter r => String -> r HS.Expr
parseTestExpr = parseTestIR

-- | Parses an IR function declaration for testing purposes.
parseTestFuncDecl :: MonadReporter r => String -> r HS.FuncDecl
parseTestFuncDecl = parseTestIR

-- | Parses an IR import declaration for testing purposes.
parseTestImportDecl :: MonadReporter r => String -> r HS.ImportDecl
parseTestImportDecl = parseTestIR

-- | Parses an IR module for testing purposes.
parseTestModule :: MonadReporter r => [String] -> r HS.Module
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
expectParseTestName :: MonadIO m => String -> m HS.Name
expectParseTestName = expectParseTestIR "name"

-- | Parses a qualifiable IR name for testing purposes and sets the
--   expectation that parsing is successful.
expectParseTestQName :: MonadIO m => String -> m HS.QName
expectParseTestQName = expectParseTestIR "qualifiable name"

-- | Parses an IR type expression for testing purposes and sets the
--   expectation that parsing is successful.
expectParseTestType :: MonadIO m => String -> m HS.Type
expectParseTestType = expectParseTestIR "type expression"

-- | Parses an IR type schema for testing purposes and sets the
--   expectation that parsing is successful.
expectParseTestTypeSchema :: MonadIO m => String -> m HS.TypeSchema
expectParseTestTypeSchema = expectParseTestIR "type schema"

-- | Parses an IR type declaration for testing purposes and sets the
--   expectation that parsing is successful.
expectParseTestTypeDecl :: MonadIO m => String -> m HS.TypeDecl
expectParseTestTypeDecl = expectParseTestIR "type declaration"

-- | Parses an IR type declaration for testing purposes and sets the
--   expectation that parsing is successful.
expectParseTestTypeSig :: MonadIO m => String -> m HS.TypeSig
expectParseTestTypeSig = expectParseTestIR "type signature"

-- | Parses an IR expression for testing purposes and sets the
--   expectation that parsing is successful.
expectParseTestExpr :: MonadIO m => String -> m HS.Expr
expectParseTestExpr = expectParseTestIR "expression"

-- | Parses an IR function declaration for testing purposes and sets the
--   expectation that parsing is successful.
expectParseTestFuncDecl :: MonadIO m => String -> m HS.FuncDecl
expectParseTestFuncDecl = expectParseTestIR "function declaration"

-- | Parses an IR import declaration for testing purposes and sets the
--   expectation that parsing is successful.
expectParseTestImportDecl :: MonadIO m => String -> m HS.ImportDecl
expectParseTestImportDecl = expectParseTestIR "import"

-- | Parses an IR module for testing purposes and sets the
--   expectation that parsing is successful.
expectParseTestModule :: MonadIO m => [String] -> m HS.Module
expectParseTestModule = expectParseTestIR "module" . unlines
