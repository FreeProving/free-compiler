module Main where


import System.Environment
import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.Extension
import Coq.Converter


main :: IO ()
main = do
    [f] <- getArgs
    s     <- readFile f
    parseAndPrintFile s


parseFile :: String -> IO ()
parseFile f = do
            s <- readFile f
            putStrLn (convertToCoq (fromParseResult (parseModuleWithMode (customParseMode f) s)))

parseAndPrintFile :: String -> IO ()
parseAndPrintFile f = do
            s <- readFile f
            putStrLn (show (fromParseResult (parseModuleWithMode (customParseMode f) s)))

customParseMode :: String -> ParseMode
customParseMode s = ParseMode s Haskell98 [] True True Nothing True
