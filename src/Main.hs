module Main where

import Language.Haskell.Exts.Extension (Language(..))
import Language.Haskell.Exts.Parser (ParseMode(..), fromParseResult, parseModuleWithMode)
import System.Environment (getArgs)

import Compiler.Converter (convertModule, printCoqAST, writeCoqFile)
import Compiler.Types (ConversionMode(..), ConversionMonad(..))

import Data.List (elemIndex)
import Data.Maybe (fromJust, isJust)

main :: IO ()
main = do
  args <- getArgs
  putStrLn (show (head args))

compileAndPrintFile :: String -> IO ()
compileAndPrintFile f = do
  args <- getArgs
  s <- readFile f
  printCoqAST
    (convertModule
       (fromParseResult (parseModuleWithMode (customParseMode f) s))
       (getMonadFromArgs args)
       (getModeFromArgs args))

compileAndSaveFile :: String -> IO ()
compileAndSaveFile f = do
  args <- getArgs
  s <- readFile f
  writeCoqFile
    (addSavePath fileName)
    (convertModule
       (fromParseResult (parseModuleWithMode (customParseMode fileName) s))
       (getMonadFromArgs args)
       (getModeFromArgs args))
  where
    fileName = getFileNameFromPath f

parseAndPrintFile :: String -> IO ()
parseAndPrintFile f = do
  s <- readFile f
  print (fromParseResult (parseModuleWithMode (customParseMode f) s))

testAst :: IO ()
testAst = parseAndPrintFile "TestModules/Test.hs"

test :: IO ()
test = compileAndPrintFile "TestModules/Test.hs"

saveTest :: IO ()
saveTest = compileAndSaveFile "TestModules/Test.hs"

addSavePath :: String -> String
addSavePath fileName = "CoqFiles/OutputFiles/" ++ fileName ++ ".v"

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
getMonadFromArgs ("-o":_) = Option
getMonadFromArgs ("-i":_) = Identity
getMonadFromArgs (_:xs) = getMonadFromArgs xs

getModeFromArgs :: [String] -> ConversionMode
getModeFromArgs [] = FueledFunction
getModeFromArgs ("-f":_) = FueledFunction
getModeFromArgs ("-h":_) = HelperFunction
getModeFromArgs (_:xs) = getModeFromArgs xs
