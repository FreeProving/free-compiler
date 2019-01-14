module Main where


import System.Environment
import Language.Haskell.Exts.Parser
import Language.Haskell.Exts.Extension
import Language.Haskell.Exts.Syntax
import Language.Haskell.Exts.SrcLoc

import Compiler.Converter
import Compiler.HelperFunctions
import Compiler.Types

import Data.List (elemIndex)
import Data.Maybe (isJust, fromJust)

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

parseAndSaveFile :: String -> IO ()
parseAndSaveFile f = do
                  args <- getArgs
                  s <- readFile f
                  writeCoqFile (addSavePath fileName) (convertModule (fromParseResult (parseModuleWithMode (customParseMode fileName) s))
                    (getMonadFromArgs args)
                      (getModeFromArgs args))
  where
    fileName = getFileNameFromPath f

parseAndPrintFile :: String -> IO ()
parseAndPrintFile f = do
            s <- readFile f
            print (fromParseResult (parseModuleWithMode (customParseMode f) s))

testAst :: IO ()
testAst = parseAndPrintFile "Test.hs"


test :: IO ()
test =
    parseFile "Test.hs"

saveTest :: IO ()
saveTest =
  parseAndSaveFile "Test.hs"

addSavePath :: String -> String
addSavePath fileName =
  "CoqFiles/OutputFiles/" ++
  fileName ++
  ".v"

getFileNameFromPath :: String -> String
getFileNameFromPath p =
  if isJust maybeStrokeIndex
    then getFileNameFromPath (drop ((fromJust maybeStrokeIndex) + 1) p)
    else take ((length p) - 3) p
  where
    maybeStrokeIndex = elemIndex '/' p


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
