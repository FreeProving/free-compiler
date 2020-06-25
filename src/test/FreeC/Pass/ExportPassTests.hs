-- | This module contains tests for "FreeC.Pass.ExportPass".

module FreeC.Pass.ExportPassTests
  ( testExportPass
  )
where

import           Test.Hspec

import           Data.Maybe                     ( fromJust )
import qualified Data.Set                      as Set
import qualified Data.Text                     as Text

import qualified FreeC.Backend.Coq.Syntax      as Coq
import           FreeC.Environment
import           FreeC.Environment.Entry
import           FreeC.Environment.ModuleInterface
import           FreeC.Monad.Class.Testable
import           FreeC.Monad.Converter
import           FreeC.Pass.ExportPass
import           FreeC.Pretty
import           FreeC.Test.Environment
import           FreeC.Test.Parser


shouldBeQualifiedWith :: Coq.Qualid -> String -> Converter Expectation
shouldBeQualifiedWith qualid modName = do
  case qualid of
    Coq.Qualified s _ -> return $ (Text.unpack s) `shouldBe` modName
    Coq.Bare _ ->
      return
        $    expectationFailure
        $    showPretty
        $    prettyString "Expected qualifier"
        <$$> line
        <>   indent 2 (prettyString modName)
        <>   line
        <$$> prettyString "but it was not qualified"

testExportPass :: SpecWith ()
testExportPass = describe "FreeC.Pass.ExportPass" $ do
  context "Exported entries are qualified when exported " $ do
    it "Names of data types should be qualified when exported" $ do
      input <- expectParseTestModule ["module A where", "data Foo = Bar"]
      shouldSucceedWith $ do
        _       <- defineTestTypeCon "Foo" 0 ["Bar"]
        _       <- defineTestCon "Bar" 0 "Foo"
        _       <- exportPass input
        mOutput <- inEnv $ lookupAvailableModule "A"
        let dEntries =
              filter isDataEntry $ Set.toList $ interfaceEntries $ fromJust
                mOutput
            foo = head dEntries
        entryIdent foo `shouldBeQualifiedWith` "A"
    it "Names of constructors are qualified when exported" $ do
      input <- expectParseTestModule ["module A where", "data ABar = Foo"]
      shouldSucceedWith $ do
        _       <- defineTestTypeCon "ABar" 0 ["Foo"]
        _       <- defineTestCon "Foo" 0 "ABar"
        _       <- exportPass input
        mOutput <- inEnv $ lookupAvailableModule "A"
        let
          cEntries =
            filter isConEntry $ Set.toList $ interfaceEntries $ fromJust mOutput
          foo = head cEntries
        entryIdent foo `shouldBeQualifiedWith` "A"
    it "Typesynonyms are qualified when exported" $ do
      input <- expectParseTestModule
        ["module A where", "data Bar = Bar;", "type Foo = Bar"]
      shouldSucceedWith $ do
        _       <- defineTestTypeCon "Bar" 0 ["Bar"]
        _       <- defineTestCon "Bar" 0 "Bar"
        _       <- defineTestTypeSyn "Foo" [] "Bar"
        _       <- exportPass input
        mOutput <- inEnv $ lookupAvailableModule "A"
        let tsEntries =
              filter isTypeSynEntry $ Set.toList $ interfaceEntries $ fromJust
                mOutput
            foo = head tsEntries
        entryIdent foo `shouldBeQualifiedWith` "A"
    it "Function definitions are qualified when exported" $ do
      input <- expectParseTestModule
        ["module A where", "data Bar = Bar;", "type Foo = Bar"]
      shouldSucceedWith $ do
        _       <- defineTestTypeCon "Foo" 0 ["Foo"]
        _       <- defineTestCon "Foo" 0 "Foo"
        _       <- defineTestFunc "mkFoo" 0 "Foo"
        _       <- exportPass input
        mOutput <- inEnv $ lookupAvailableModule "A"
        let fEntries =
              filter isFuncEntry $ Set.toList $ interfaceEntries $ fromJust
                mOutput
            mkFoo = head fEntries
        entryIdent mkFoo `shouldBeQualifiedWith` "A"
