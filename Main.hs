module Main where


import System.Environment
import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.Extension
import Language.Haskell.Exts.Syntax
import Language.Haskell.Exts.SrcLoc
import Coq.Converter


main :: IO ()
main = do
    [f] <- getArgs
    s     <- readFile f
    parseAndPrintFile s


parseFile :: String -> IO ()
parseFile f = do
            s <- readFile f
            printCoqAST (convertModule (fromParseResult (parseModuleWithMode (customParseMode f) s)))

parseAndPrintFile :: String -> IO ()
parseAndPrintFile f = do
            s <- readFile f
            putStrLn (show (fromParseResult (parseModuleWithMode (customParseMode f) s)))

testAst :: IO ()
testAst = parseAndPrintFile "Test.hs"

test :: IO ()
test = parseFile "Test.hs"

customParseMode :: String -> ParseMode
customParseMode s = ParseMode s Haskell98 [] True True Nothing True
