module Compiler.Language.Coq.Pretty
  ( printCoqAST
  , writeCoqFile
  )
where

import           System.IO

import qualified Data.Text                     as T
import qualified Data.Text.Lazy                as TL
import           Text.PrettyPrint.Leijen.Text   ( Doc
                                                , SimpleDoc
                                                , (<$$>)
                                                , empty
                                                , displayIO
                                                , renderPretty
                                                )

import qualified Language.Coq.Gallina          as G
import           Language.Coq.Pretty            ( renderGallina )

import           Compiler.Language.Coq.Preamble ( importDefinitions )
import           Compiler.Types                 ( ConversionMonad(..) )


-- | Pretty prints the given Coq AST and concatenates the resulting
--   @Doc@s with newlines.
prettyCoqAst :: [G.Sentence] -> Doc
prettyCoqAst = foldr (<$$>) empty . map renderGallina

-- | Pretty prints and renders the given Coq AST with a maximum line length of
--   @width@ characters of which only @ribbonWidth@ characters may be non
--   indentation characters.
renderCoqAst :: [G.Sentence] -> SimpleDoc
renderCoqAst = renderPretty ribbonFrac width . prettyCoqAst
 where
  ribbonWidth, width :: Int
  ribbonWidth = 80
  width       = 120

  ribbonFrac :: Float
  ribbonFrac = fromIntegral ribbonWidth / fromIntegral width

-- | Pretty prints and writes a Coq AST to the given file handle.
hPutCoqAst :: Handle -> G.Sentence -> ConversionMonad -> IO ()
hPutCoqAst handle sentence cMonad =
  -- TODO the preamble should be added by the converter and
  -- not the pretty printer.
  displayIO handle $ renderCoqAst (importDefinitions cMonad ++ [sentence])

-- | Pretty prints and writes a Coq AST to @stdout@.
printCoqAST :: G.Sentence -> ConversionMonad -> IO ()
printCoqAST = hPutCoqAst stdout

-- | Pretty prints and writes a Coq AST to the given file.
writeCoqFile :: String -> G.Sentence -> ConversionMonad -> IO ()
writeCoqFile path sentence cMonad =
  withFile path WriteMode (\handle -> hPutCoqAst handle sentence cMonad)
