module Main where


import System.Environment
import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.Extension
import Language.Haskell.Exts.Syntax
import Language.Haskell.Exts.SrcLoc

import Compiler.Converter
import Compiler.HelperFunctions
import Compiler.Types 

main :: IO ()
main = do
    args <- getArgs
    putStrLn $ head args

parseFile :: String -> IO ()
parseFile f = do
            args <- getArgs
            s <- readFile f
            printCoqAST (convertModule
                          (fromParseResult (parseModuleWithMode (customParseMode f) s))
                            (getMonadFromArgs args)
                              (getModeFromArgs args))

parseAndPrintFile :: String -> IO ()
parseAndPrintFile f = do
            s <- readFile f
            print (fromParseResult (parseModuleWithMode (customParseMode f) s))

testAst :: IO ()
testAst = parseAndPrintFile "Test.hs"


test :: IO ()
test =
    parseFile "Test.hs"


customParseMode :: String -> ParseMode
customParseMode s = ParseMode s Haskell98 [] True True Nothing True

getMonadFromArgs :: [String] -> ConversionMonad
getMonadFromArgs [] = Option
getMonadFromArgs ("-o" : _ ) = Option
getMonadFromArgs ("-i" : _ ) = Identity
getMonadFromArgs ( _ : xs) = getMonadFromArgs xs

getModeFromArgs :: [String] -> ConversionMode
getModeFromArgs [] = FueledFunction
getModeFromArgs ("-f" : _ ) = FueledFunction
getModeFromArgs ("-h" : _ ) = HelperFunction
getModeFromArgs ( _ : xs ) = getModeFromArgs xs
