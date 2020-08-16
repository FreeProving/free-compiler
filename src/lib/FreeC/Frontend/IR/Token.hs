-- | This module contains the token data type for the intermediate language.
module FreeC.Frontend.IR.Token
  ( -- * Tokens
    Token(..)
  , mkIdentToken
  , mkSymbolToken
    -- * Special symbols
  , specialSymbols
    -- * Keywords
  , Keyword(..)
  , keywords
  ) where

import           Data.Char        ( isUpper )
import           Data.Tuple.Extra ( (&&&) )

import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Tokens                                                                    --
-------------------------------------------------------------------------------
-- | The token classes of the intermediate language.
--
--   In the description of the grammar for the token classes below, we are
--   using the following character classes.
--
--   > <lower>   ::= "a" | … | "z" | <any lowercase Unicode letter>
--   > <upper>   ::= "A" | … | "Z" | <any upper- or titlecase Unicode letter>
--   >
--   > <numeric> ::= <digit> | <any Unicode numeric character>
--   > <digit>   ::= "0" | … | "9"
--   > <octit>   ::= "0" | … | "7"
--   > <hexit>   ::= "0" | … | "9" | "a" | … | "f" | "A" | … | "F"
--   >
--   > <symbol>  ::= <any Unicode symbol or punctuation>
--   > <graphic> ::= <lower> | <upper> | <symbol> | <numeric>
--   > <space>   ::= " "
--
--   == Identifiers
--
--   Identifiers can contain letters (both upper- and lowercase), digits,
--   underscores and apostrophes. However, identifiers must not start with an
--   digit or apostrophe. Identifiers starting with an uppercase letter
--   identify constructors.
--
--   > <identletter> ::= <lower> | <upper> | <numeric> | "_" | "'"
--   > <varid>  ::= (<lower> | "_") { <identletter> }
--   > <conid>  ::= <upper> { <identletter> }
--
--   == Symbolic names
--
--   Symbolic names are sequences of arbitrary Unicode symbol and punctuation
--   characters wrapped in parenthesis where no parenthesis are allowed in the
--   name itself.
--
--   Constructor symbols are either empty or start with one of @"["@, @":"@
--   or @","@. The @"["@ and @","@ start characters are needed in addition
--   to @":"@ (which is the start character of constructor symbols in Haskell)
--   such that the empty list constructor and tuple constructors are recognized
--   correctly.
--
--   > <namesymbol>  ::= <symbol> \ ( "(" | ")" )
--   > <consymstart> ::= "[" | ":" | ","
--   >
--   > <varsym> ::= "(" (<namesymbol> \ <consymstart>) { <namesymbol> } ")"
--   > <consym> ::= "(" [ <consymstart> { <namesymbol> } ] ")"
--
--   == Integers
--
--   Integer tokens have an optional sign and can be in decimal, octal or
--   hexadecimal notation. The prefixes of octal and hexadecimal integers
--   as well as the digits (or "hexits") of hexadecimal integers are case
--   insensitive.
--
--   > <decimal>     ::= <digit> { <digit> }
--   > <octal>       ::= <octit> { <octit> }
--   > <hexadecimal> ::= <hexit> { <hexit> }
--   >
--   > <integer>   ::= [ "+" | "-" ] <natural>
--   > <natural>   ::= <decimal>
--   >               | "0o" <octal>       | "0O" <octal>
--   >               | "0x" <hexadecimal> | "0X" <hexadecimal>
--
--   == Strings
--
--   Strings are wrapped in double quotes. They can contain arbitrary Unicode
--   letters, digits, symbols and punctuation characters as well as spaces
--   and escape sequences.
--
--   > <escape> ::= <any Haskell escape sequence>
--   > <gap>    ::= "\" { <arbitrary Unicode whitespace> } "\"
--   >
--   > <string> ::= '"' { <graphic> \ ( '"' | "\" )
--   >                  | <space>
--   >                  | <escape>
--   >                  | <gap>
--   >                  } '"'
data Token
  = ConIdent String  -- ^ @<conid>@ a constructor identifier.
  | ConSymbol String -- ^ @<consym>@ a constructor symbol.
  | VarIdent String  -- ^ @<varid>@ a variable identifier.
  | VarSymbol String -- ^ @<varsym>@ a variable symbol.
  | Keyword Keyword  -- ^ A t'Keyword'.
  | IntToken Integer -- ^ @<integer>@ an integer literal.
  | StrToken String  -- ^ @<string>@ a string literal.
  | At               -- ^ @"\@"@
  | Comma            -- ^ @","@
  | Dot              -- ^ @"."@
  | DoubleColon      -- ^ @"::"@
  | Equals           -- ^ @"="@
  | Lambda           -- ^ @"\\"@
  | LBrace           -- ^ @"{"@
  | LParen           -- ^ @"("@
  | Pipe             -- ^ @"|"@
  | RBrace           -- ^ @"}"@
  | RParen           -- ^ @")"@
  | RArrow           -- ^ @"->"@
  | Semi             -- ^ @";"@
  | Bang             -- ^ @"!"@
 deriving ( Eq, Show )

-- | Constructs a 'ConIdent', 'VarIdent', 'Keyword' for the given identifier
--   or keyword depending.
--
--   Constructors and variables can be told apart by the case of their first
--   character. Constructors start with upper case letters and variables with
--   lower case letters or an underscore.
--
--   If the given string occurs in 'keywords', the corresponding keyword
--   token is returned instead.
mkIdentToken :: String -> Token
mkIdentToken ident = case lookup ident keywords of
  Nothing
    | isUpper (head ident) -> ConIdent ident
    | otherwise -> VarIdent ident
  Just keyword -> Keyword keyword

-- | Constructs a 'ConSymbol' or 'VarSymbol' for the given symbolic name.
--
--   The given string should not include the parenthesis around symbols.
--
--   Constructor symbols must be empty or start with one of @"["@, @":"@ or
--   @","@.
mkSymbolToken :: String -> Token
mkSymbolToken "" = ConSymbol ""
mkSymbolToken sym@(first : _)
  | first `elem` [ '[', ':', ',' ] = ConSymbol sym
mkSymbolToken sym = VarSymbol sym

-- | Pretty prints a token.
instance Pretty Token where
  pretty (ConIdent ident) = prettyString ident
  pretty (ConSymbol sym)
    = prettyString "(" <> prettyString sym <> prettyString ")"
  pretty (VarIdent ident) = prettyString ident
  pretty (VarSymbol sym)
    = prettyString "(" <> prettyString sym <> prettyString ")"
  pretty (Keyword keyword) = pretty keyword
  pretty (IntToken value) = pretty value
  pretty (StrToken value) = prettyString (show value)
  pretty At = prettyString "@"
  pretty Comma = prettyString ","
  pretty Dot = prettyString "."
  pretty DoubleColon = prettyString "::"
  pretty Equals = prettyString "="
  pretty Lambda = prettyString "\\"
  pretty LBrace = prettyString "{"
  pretty LParen = prettyString "("
  pretty Pipe = prettyString "|"
  pretty RBrace = prettyString "}"
  pretty RParen = prettyString ")"
  pretty RArrow = prettyString "->"
  pretty Semi = prettyString ";"
  pretty Bang = prettyString "!"

-------------------------------------------------------------------------------
-- Special symbols                                                           --
-------------------------------------------------------------------------------
-- | Symbols that cannot be used as symbolic names.
--
--   Since the intermediate language is only parsed in tests, this
--   constraints only the identifiers that can be used in tests.
--   If the IR AST is generated by the frontend, identifiers are
--   allowed to collide with keywords.
specialSymbols :: [ (String, Token) ]
specialSymbols = map (showPretty &&& id)
  [ At
  , Comma
  , Dot
  , DoubleColon
  , Equals
  , Lambda
  , LBrace
  , LParen
  , Pipe
  , RBrace
  , RParen
  , RArrow
  , Semi
  , Bang
  ]

-------------------------------------------------------------------------------
-- Keywords                                                                  --
-------------------------------------------------------------------------------
-- Data type for keyword 'Token's.
data Keyword
  = CASE      -- ^ @"case"@
  | DATA      -- ^ @"data"@
  | ELSE      -- ^ @"else"@
  | ERROR     -- ^ @"error"@
  | FORALL    -- ^ @"forall"@
  | IF        -- ^ @"if"@
  | IMPORT    -- ^ @"import"@
  | IN        -- ^ @"in"@
  | LET       -- ^ @"let"@
  | MODULE    -- ^ @"module"@
  | OF        -- ^ @"of"@
  | THEN      -- ^ @"then"@
  | TYPE      -- ^ @"type"@
  | UNDEFINED -- ^ @"undefined"@
  | WHERE     -- ^ @"where"@
 deriving ( Eq, Show )

-- | Maps reserved words that cannot be used as identifiers to the
--   corresponding 'Keyword' tokens.
--
--   Since the intermediate language is only parsed in tests, this
--   constraints only the identifiers that can be used in tests.
--   If the IR AST is generated by the frontend, identifiers are
--   allowed to collide with keywords.
keywords :: [ (String, Keyword) ]
keywords = map (showPretty &&& id)
  [ CASE
  , DATA
  , ELSE
  , ERROR
  , FORALL
  , IF
  , IMPORT
  , IN
  , LET
  , MODULE
  , OF
  , THEN
  , TYPE
  , UNDEFINED
  , WHERE
  ]

-- | Pretty prints a keyword.
instance Pretty Keyword where
  pretty CASE      = prettyString "case"
  pretty DATA      = prettyString "data"
  pretty ELSE      = prettyString "else"
  pretty ERROR     = prettyString "error"
  pretty FORALL    = prettyString "forall"
  pretty IF        = prettyString "if"
  pretty IMPORT    = prettyString "import"
  pretty IN        = prettyString "in"
  pretty LET       = prettyString "let"
  pretty MODULE    = prettyString "module"
  pretty OF        = prettyString "of"
  pretty THEN      = prettyString "then"
  pretty TYPE      = prettyString "type"
  pretty UNDEFINED = prettyString "undefined"
  pretty WHERE     = prettyString "where"
