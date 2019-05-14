{-# LANGUAGE LambdaCase, OverloadedStrings #-}

module Language.Coq.InfixNames (
  identIsVariable,
  infixToPrefix, toPrefix, toLocalPrefix,
  prefixOpToInfix,
  infixToCoq,
  identIsOp, identToOp,
  splitModule -- a bit out of place here. oh well.
  ) where

import Control.Lens

import Control.Applicative
import Control.Monad
import Data.Semigroup (Semigroup(..))
import Data.Char
import Data.Text (Text)
import qualified Data.Text as T
import Text.Parsec hiding ((<|>), many)



--------------------------------------------------------------------------------

-- Lets keep this module self-contained (but use the same type synonyms)
type Op = T.Text
type Ident = T.Text
type ModuleIdent = T.Text
type AccessIdent = T.Text

identIsVariable_ :: Text -> Bool
identIsVariable_ = T.uncons <&> \case
  Just (h,t) -> (isAlpha h || h == '_') && T.all (\c -> isAlphaNum c || c == '_' || c == '\'') t
  Nothing    -> False

identIsVariable :: Text -> Bool
identIsVariable = all identIsVariable_ . T.splitOn "."

-- An operator's user-facing name in Coq (a notation)
infixToPrefix :: Op -> Ident
infixToPrefix = ("_" <>) . (<> "_")

toPrefix :: Ident -> Ident
toPrefix x | identIsVariable x = x
           | otherwise         = infixToCoq x

toLocalPrefix :: Ident -> Ident
toLocalPrefix x | identIsVariable x = x
                | otherwise         = "l" <> infixToCoq x

prefixOpToInfix :: Ident -> Maybe Op
prefixOpToInfix px = do
  x <- T.stripSuffix "_" =<< T.stripPrefix "_" px
  guard . not $ identIsVariable x
  pure x

-- An operator's defined name in Coq (hidden by a notation)
infixToCoq_ :: Op -> Ident
infixToCoq_ name = "op_" <> T.pack (T.unpack name) <> "__"

-- This is code smell: Why do we return an unstructured Ident, and not a QualId?
infixToCoq :: Op -> Ident
infixToCoq op = case splitModule op of
    Just (m,op) -> m <> "." <> infixToCoq_ op
    Nothing     -> infixToCoq_ op

splitModule :: Ident -> Maybe (ModuleIdent, AccessIdent)
splitModule = fmap fixup . either (const Nothing) Just . parse qualid "" where
  qualid = do
    let modFrag = T.cons <$> upper <*> (T.pack <$> many (alphaNum <|> char '_' <|> char '\''))
    mod <- T.intercalate "." <$> many1 (try (modFrag <* char '.'))
    base <- T.pack <$> some anyChar -- since we're assuming we get a valid name
    pure $ (mod, base)

  -- When we have a module name that ends in .Z or .N then that should be
  -- considered part of the name of the function. This is a hack to make the
  -- common case of working with names like Coq.ZArith.BinInt.Z.eqb more convenient,
  -- without solving the problem of handling non-filesystem-modules in general
  fixup (mod, name)
    | ".Z" `T.isSuffixOf` mod = (T.take (T.length mod - 2) mod, "Z." <> name)
    | ".N" `T.isSuffixOf` mod = (T.take (T.length mod - 2) mod, "N." <> name)
    | otherwise               = (mod, name)

identIsOp :: Ident -> Bool
identIsOp t = "op_" `T.isPrefixOf` t && "__" `T.isSuffixOf` t
    -- the next clause is a work-around as long as the dict accessors are named
    -- op_...____ – these do not have notations
    && not ("____" `T.isSuffixOf` t)
    && T.length t > 5

identToOp :: Ident -> Maybe Op
identToOp t
   | identIsOp t = Just $ T.pack (T.unpack (T.drop 3 (T.dropEnd 2 t)))
   | otherwise   = Nothing
