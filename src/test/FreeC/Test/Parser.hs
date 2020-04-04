-- | This module contains utility functions for tests that have to parse
--   the intermediate representation.
--
--   There is one general function that works with any AST node that has a
--   'Parseable' instance as well as a specialized function for each AST
--   node with a 'Parseable' instance. The specialized functions are mainly
--   to be used for documentation purposes and to avoid expression type
--   signatures in places where Haskell cannot infer the type of the node
--   to parse.

module FreeC.Test.Parser where

import           FreeC.IR.SrcSpan
import           FreeC.Frontend.IR.Parser
import qualified FreeC.IR.Syntax               as HS
import           FreeC.Monad.Reporter

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
parseTestFuncDeclParser :: MonadReporter r => String -> r HS.FuncDecl
parseTestFuncDeclParser = parseTestIR

-- | Parses an IR import declaration for testing purposes.
parseTestImportDecl :: MonadReporter r => String -> r HS.ImportDecl
parseTestImportDecl = parseTestIR

-- | Parses an IR module for testing purposes.
parseTestModule :: MonadReporter r => [String] -> r HS.Module
parseTestModule = parseTestIR . unlines
