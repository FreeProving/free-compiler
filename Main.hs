module Main where

import System.Environment
import Language.Haskell.Exts.Parser

main :: IO ()
main = do
    [f] <- getArgs
    s     <- readFile f
    parseAndPrint s

parseAndPrint f = writeFile "output/test.txt" (show (fromParseResult (parseModuleWithComments defaultParseMode f)))
