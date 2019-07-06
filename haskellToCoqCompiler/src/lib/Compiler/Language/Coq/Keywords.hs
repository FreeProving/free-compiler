module Compiler.Language.Coq.Keywords where

-- | Keywords of the Gallina specification language.
--
--   This list has been taken from the Coq documentation
--   <https://coq.inria.fr/refman/language/gallina-specification-language.html>.
coqKeywords :: [String]
coqKeywords =
  [ "as"
  , "at"
  , "cofix"
  , "else"
  , "end"
  , "exists"
  , "exists2"
  , "fix"
  , "for"
  , "forall"
  , "fun"
  , "if"
  , "IF"
  , "in"
  , "let"
  , "match"
  , "mod"
  , "Prop"
  , "return"
  , "Set"
  , "then"
  , "Type"
  , "using"
  , "where"
  , "with"
  ]
