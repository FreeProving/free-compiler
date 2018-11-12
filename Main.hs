module Main where

import System.Environment
import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.Extension

main :: IO ()
main = do
    [f] <- getArgs
    s     <- readFile f
    parseAndPrint s

parseAndPrint f = writeFile "test.txt" (show (fromParseResult (parseModuleWithComments defaultParseMode f)))

parseFile f = do
            s <- readFile f
            putStrLn (show (fromParseResult (parseModuleWithMode (myParseMode f) s)))

myParseMode s = ParseMode s Haskell98 [] True True Nothing True
