-- | This module exports lists for keywords of the Agda language.
module FreeC.Backend.Agda.Keywords where

-- | Identifiers that cannot be used in Agda, because they are keywords
--
--   This list contains all keywords from the Agda docs
--   <https://agda.readthedocs.io/en/v2.6.1/language/lexical-structure.html#keywords-and-special-symbols>.
agdaKeywords :: [String]
agdaKeywords
  = [ "abstract"
    , "constructor"
    , "data"
    , "do"
    , "eta-equality"
    , "field"
    , "forall"
    , "hiding"
    , "import"
    , "in"
    , "inductive"
    , "infix"
    , "infixl"
    , "infixr"
    , "instance"
    , "let"
    , "macro"
    , "module"
    , "mutual"
    , "no-eta-equality"
    , "open"
    , "overlap"
    , "pattern"
    , "postulate"
    , "primitive"
    , "private"
    , "public"
    , "quote"
    , "quoteContext"
    , "quoteGoal"
    , "quoteTerm"
    , "record"
    , "renaming"
    , "rewrite"
    , "Set"
    , "syntax"
    , "tactic"
    , "unquote"
    , "unquoteDecl"
    , "unquoteDef"
    , "using"
    , "variable"
    , "where"
    , "with"
    ]
