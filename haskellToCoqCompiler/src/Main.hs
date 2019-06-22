module Main where

import System.Environment (getArgs)

import Compiler.Converter (convertModule)
import Compiler.Language.Coq.Pretty (printCoqAST, writeCoqFile)
import Compiler.Language.Haskell.Parser (parseModuleFile)
import Compiler.Types (ConversionMonad(..))

import Data.List (elemIndex)
import Data.Maybe (fromJust, isJust)

-- TODO a proper command line interface would be handy.
main :: IO ()
main = do
  args <- getArgs
  compileAndPrintFile (head args)

compileAndPrintFile :: String -> IO ()
compileAndPrintFile f = do
  args <- getArgs
  ast <- parseModuleFile f
  printCoqAST
    (convertModule
       ast
       (getMonadFromArgs args))
    (getMonadFromArgs args)

compileAndSaveFile :: String -> IO ()
compileAndSaveFile f = do
  args <- getArgs
  ast <- parseModuleFile f
  writeCoqFile
    (addSavePath fileName)
    (convertModule
       ast
       (getMonadFromArgs args))
    (getMonadFromArgs args)
  where
    fileName = getFileNameFromPath f

parseAndPrintFile :: String -> IO ()
parseAndPrintFile f = do
  ast <- parseModuleFile f
  print ast

testAst :: IO ()
testAst = parseAndPrintFile "TestModules/Test.hs"

test :: IO ()
test = compileAndPrintFile "TestModules/Test.hs"

saveTest :: IO ()
saveTest = compileAndSaveFile "TestModules/Test.hs"

savePrelude :: IO ()
savePrelude = compileAndSaveFile "TestModules/Prelude.hs"

addSavePath :: String -> String
addSavePath fileName = "CoqFiles/OutputFiles/" ++ fileName ++ ".v"

getFileNameFromPath :: String -> String
getFileNameFromPath p =
  if isJust maybeStrokeIndex
    then getFileNameFromPath (drop ((fromJust maybeStrokeIndex) + 1) p)
    else take ((length p) - 3) p
  where
    maybeStrokeIndex = elemIndex '/' p

getMonadFromArgs :: [String] -> ConversionMonad
getMonadFromArgs [] = Option
getMonadFromArgs ("-o":_) = Option
getMonadFromArgs ("-i":_) = Identity
getMonadFromArgs (_:xs) = getMonadFromArgs xs
