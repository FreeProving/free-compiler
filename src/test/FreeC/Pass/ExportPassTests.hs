-- | This module contains tests for "FreeC.Pass.ExportPass".
module FreeC.Pass.ExportPassTests ( testExportPass ) where

import           Data.List                         ( find )
import           Data.Maybe                        ( fromJust )
import qualified Data.Set                          as Set
import           Test.Hspec

import qualified FreeC.Backend.Coq.Syntax          as Coq
import           FreeC.Environment
import           FreeC.Environment.Entry
import           FreeC.Environment.ModuleInterface
import qualified FreeC.IR.Syntax                   as IR
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Pass.ExportPass
import           FreeC.Pretty
import           FreeC.Test.Environment
import           FreeC.Test.Parser

-- | Looks up an exported entry in the given module interface
--   but does not check if the entry is defined in the given module.
lookupExportedEntry :: IR.Scope -> IR.QName -> ModuleInterface -> Maybe EnvEntry
lookupExportedEntry scope qname moduleInterface = find
  (((scope, qname) ==) . entryScopedName)
  (Set.toList $ interfaceEntries moduleInterface)

-- | Checks if the given 'Coq.Qualid' is qualified and compares the qualifier
--   to the given module name.
shouldBeQualifiedWith :: Coq.Qualid -> String -> Converter Expectation
shouldBeQualifiedWith qualid modNameStr = do
  case qualid of
    Coq.Qualified s _ -> return $ s `shouldBe` Coq.ident modNameStr
    Coq.Bare _        -> return
      $ expectationFailure
      $ showPretty
      $ prettyString "Expected qualifier" <$$> line
      <> indent 2 (prettyString modNameStr)
      <> line <$$> prettyString "but it was not qualified"

-- | Test group for 'exportPass' tests.
testExportPass :: Spec
testExportPass = describe "FreeC.Pass.ExportPass"
  $ do
    context "qualifies Coq identifiers of exported entries"
      $ do
        it "qualifies Coq identifiers of data type entries"
          $ do
            input
              <- expectParseTestModule ["module A where", "data A.Foo = A.Bar"]
            shouldSucceedWith
              $ do
                _ <- defineTestTypeCon "A.Foo" 0 ["A.Bar"]
                _ <- defineTestCon "A.Bar" 0 "A.Foo"
                _ <- exportPass input
                mOutput <- inEnv $ lookupAvailableModule "A"
                let foo = fromJust
                      $ lookupExportedEntry IR.TypeScope
                      (IR.Qual "A" (IR.Ident "Foo")) (fromJust mOutput)
                entryIdent foo `shouldBeQualifiedWith` "A"
        it "qualifies Coq identifiers of constructor entries"
          $ do
            input
              <- expectParseTestModule ["module A where", "data A.Bar = A.Foo"]
            shouldSucceedWith
              $ do
                _ <- defineTestTypeCon "A.Bar" 0 ["A.Foo"]
                _ <- defineTestCon "A.Foo" 0 "A.Bar"
                _ <- exportPass input
                mOutput <- inEnv $ lookupAvailableModule "A"
                let foo = fromJust
                      $ lookupExportedEntry IR.ValueScope
                      (IR.Qual "A" (IR.Ident "Foo")) (fromJust mOutput)
                entryIdent foo `shouldBeQualifiedWith` "A"
        it "qualifies Coq identifiers of type synonym entries"
          $ do
            input <- expectParseTestModule
              ["module A where", "data A.Bar = A.Bar;", "type A.Foo = A.Bar"]
            shouldSucceedWith
              $ do
                _ <- defineTestTypeCon "A.Bar" 0 ["A.Bar"]
                _ <- defineTestCon "A.Bar" 0 "A.Bar"
                _ <- defineTestTypeSyn "A.Foo" [] "A.Bar"
                _ <- exportPass input
                mOutput <- inEnv $ lookupAvailableModule "A"
                let foo = fromJust
                      $ lookupExportedEntry IR.TypeScope
                      (IR.Qual "A" (IR.Ident "Foo")) (fromJust mOutput)
                entryIdent foo `shouldBeQualifiedWith` "A"
        it "qualifies Coq identifiers of function declaration entries"
          $ do
            input <- expectParseTestModule
              ["module A where", "data A.Bar = A.Bar;", "type A.Foo = A.Bar"]
            shouldSucceedWith
              $ do
                _ <- defineTestTypeCon "A.Foo" 0 ["A.Foo"]
                _ <- defineTestCon "A.Foo" 0 "A.Foo"
                _ <- defineTestFunc "A.mkFoo" 0 "A.Foo"
                _ <- exportPass input
                mOutput <- inEnv $ lookupAvailableModule "A"
                let mkFoo = fromJust
                      $ lookupExportedEntry IR.ValueScope
                      (IR.Qual "A" (IR.Ident "mkFoo")) (fromJust mOutput)
                entryIdent mkFoo `shouldBeQualifiedWith` "A"
        it "does not override qualification of Coq identifiers for entries"
          $ do
            _ <- expectParseTestModule ["module A where", "data A.Foo = A.Foo"]
            input <- expectParseTestModule ["module B where", "import A"]
            shouldSucceedWith
              $ do
                _ <- defineTestTypeCon "A.Foo" 0 ["A.Foo"]
                _ <- defineTestCon "A.Foo" 0 "A.Foo"
                name <- parseTestQName "A.Foo"
                let qualid = Coq.Qualified (Coq.ident "A") (Coq.ident "Foo")
                modifyEnv $ modifyEntryIdent IR.TypeScope name qualid
                _ <- exportPass input
                mOutput <- inEnv $ lookupAvailableModule "B"
                let foo = fromJust
                      $ lookupExportedEntry IR.TypeScope name (fromJust mOutput)
                entryIdent foo `shouldBeQualifiedWith` "A"
