-- | This module contains a scanner for the intermediate language that takes
--   the source code and converts it into a token stream.
--
--   We convert the source code to a token stream such that
--   "FreeC.Frontend.IR.Parser" does not have to handle white
--   space explicitly.

module FreeC.Frontend.IR.Scanner
  ( TokenWithPos(..)
  , scan
  )
where

import           Data.Char                      ( isNumber
                                                , isPunctuation
                                                , isSymbol
                                                )
import           Text.Parsec                    ( Parsec
                                                , (<|>)
                                                )
import qualified Text.Parsec                   as Parsec
import qualified Text.Parsec.Token             as Parsec

import           FreeC.Frontend.IR.Token
import           FreeC.IR.SrcSpan
import           FreeC.Util.Predicate           ( (.||.)
                                                , (.&&.)
                                                )
import           FreeC.Monad.Reporter
import           FreeC.Pretty
import           FreeC.Util.Parsec

------------------------------------------------------------------------------
-- Type synonyms                                                            --
------------------------------------------------------------------------------

-- | Type of parsers for IR lexeme of type @a@.
type Scanner a = Parsec String () a

-- | A 'Token' and its position in the source code.
data TokenWithPos = TokenWithPos
  { getTokenPos :: Parsec.SourcePos
  , getToken    :: Token
  }

-- | We need a show instance for tokens with positions such that the parser
--   can print unexpected tokens.
instance Show TokenWithPos where
  show = showPretty . getToken

-- | Converts the given scanner for a token to a scanner for the same token
--   that attaches source location information.
tokenWithPos :: Scanner Token -> Scanner TokenWithPos
tokenWithPos scanner = TokenWithPos <$> Parsec.getPosition <*> scanner

------------------------------------------------------------------------------
-- Character classes                                                        --
------------------------------------------------------------------------------

-- | Scanner for a lowercase character.
--
--   > <lower> ::= "a" | … | "z" | <any lowercase Unicode letter>
lowerScanner :: Scanner Char
lowerScanner = Parsec.lower

-- | Scanner for an uppercase character.
--
--   > <upper> ::= "A" | … | "Z" | <any upper- or titlecase Unicode letter>
upperScanner :: Scanner Char
upperScanner = Parsec.upper

-- | Scanner for an Unicode numeric character.
--
--   > <numeric> ::= <digit> | <any Unicode numeric character>
numericScanner :: Scanner Char
numericScanner = Parsec.satisfy isNumber

------------------------------------------------------------------------------
-- Language Definition                                                      --
------------------------------------------------------------------------------

-- | Block comments start with @"{- "@ and can be nested.
--
--   Block comments start and end with a space such that we are still
--   able to parser pragmas which start with @"{-#"@ and end with @"#-}"@
blockCommentStart :: String
blockCommentStart = "{- "

-- | Block comments end with @" -}"@ and can be nested.
--
--   Block comments start and end with a space such that we are still
--   able to parser pragmas which start with @"{-#"@ and end with @"#-}"@
blockCommentEnd :: String
blockCommentEnd = " -}"

-- | Line comments start with @"-- "@ and span the remaining line.
lineCommentStart :: String
lineCommentStart = "-- "

-- | Valid start characters of variable identifiers
--   (see 'VarIdent' for the definition of @<varid>@).
--
--   It matches the start of the identifier only, i.e., @<lower> | "_"@.
--   The remaining characters are scanned by 'identLetter'.
varIdentStart :: Scanner Char
varIdentStart = lowerScanner <|> Parsec.char '_'

-- | Valid start characters of constructor identifiers
--   (see 'ConIdent' for the definition of @<conid>@).
--
--   It matches the start of the identifier only, i.e., @<upper>@.
--   The remaining characters are scanned by 'identLetter'.
conIdentStart :: Scanner Char
conIdentStart = upperScanner

-- | Valid non-start characters of identifiers.
--
--   This scanner is used for both @<varid>@s and @<conid>@s
--   (see 'VarIdent' and 'ConIdent' respectively).
--
--   It matches only one character at a time and only the characters after
--   the first letter.
--
--   > <identletter> ::= <lower> | <upper> | <numeric> | "_" | "'"
--
--   The start of identifiers is scanned by 'varIdentStart' and 'conIdentStart'
--   respectively.
identLetter :: Scanner Char
identLetter =
  lowerScanner <|> upperScanner <|> numericScanner <|> Parsec.oneOf "_'"

-- | Valid characters in symbolic names (i.e., in @<varsym>@ and @<consym>@,
--   see also VarIdent and 'ConIdent').
--
--   All Unicode symbol and punctuation characters except for parenthesis
--   are allowed in symbolic names. Parenthesis are not allowed since the
--   symbolic names are wrapped in parenthesis themselves.
--
--   > <symbol>     ::= <any Unicode symbol or punctuation>
--   > <namesymbol> ::= <symbol> \ ( "(" | ")" )
nameSymbolChar :: Scanner Char
nameSymbolChar =
  Parsec.satisfy ((isSymbol .||. isPunctuation) .&&. (`notElem` ['(', ')']))

-- | Language definition for the intermediate language.
--
--   Contains the parameters for the 'tokenParser' for the IR.
languageDef :: Parsec.LanguageDef ()
languageDef = Parsec.LanguageDef
  { Parsec.commentStart    = blockCommentStart
  , Parsec.commentEnd      = blockCommentEnd
  , Parsec.commentLine     = lineCommentStart
  , Parsec.nestedComments  = True
  , Parsec.identStart      = varIdentStart <|> conIdentStart
  , Parsec.identLetter     = identLetter
  , Parsec.opStart         = nameSymbolChar
  , Parsec.opLetter        = nameSymbolChar
  , Parsec.reservedNames   = [] -- Keywords are handled by 'identScanner'.
  , Parsec.reservedOpNames = [] -- Handled by order in 'tokenScanner'.
  , Parsec.caseSensitive   = True
  }

------------------------------------------------------------------------------
-- Generated lexical parsers                                                --
------------------------------------------------------------------------------

-- | Contains lexical parsers for the intermediate language.
tokenParser :: Parsec.TokenParser ()
tokenParser = Parsec.makeTokenParser languageDef

-- | Scanner for zero or more white space characters or comments.
whiteSpaceScanner :: Scanner ()
whiteSpaceScanner = Parsec.whiteSpace tokenParser

-- | Scanner for 'ConIdent' and 'VarIdent' tokens.
identScanner :: Scanner Token
identScanner = mkIdentToken <$> Parsec.identifier tokenParser

-- | Scanner for 'ConSymbol' and 'VarSymbol' tokens.
symbolScanner :: Scanner Token
symbolScanner = Parsec.between
  (Parsec.char '(')
  (Parsec.char ')')
  (mkSymbolToken <$> Parsec.option "" (Parsec.operator tokenParser))

-- | Scanner for 'IntToken's.
integerScanner :: Scanner Token
integerScanner = IntToken <$> Parsec.integer tokenParser

-- | Scanner for 'StrToken's.
stringScanner :: Scanner Token
stringScanner = StrToken <$> Parsec.stringLiteral tokenParser

-- | Scanners for tokens listed in 'specialSymbols'.
specialSymbolScanners :: [Scanner Token]
specialSymbolScanners = map
  (\(symbol, token) -> Parsec.symbol tokenParser symbol >> return token)
  specialSymbols

-- | Scanner for a single 'Token'.
tokenScanner :: Scanner TokenWithPos
tokenScanner =
  tokenWithPos
    $ Parsec.choice
    $ map Parsec.try
    $ identScanner
    : symbolScanner
    : integerScanner
    : stringScanner
    : specialSymbolScanners

-- | A scanner for zero or more 'Token's.
--
--   White spaces and comments before and between tokens are ignored.
tokenListScanner :: Scanner [TokenWithPos]
tokenListScanner =
  whiteSpaceScanner
    *> Parsec.many (Parsec.lexeme tokenParser tokenScanner)
    <* Parsec.eof

-- | Converts the given IR source code to a stream of IR tokens.
--
--   Reports a fatal error if there are unknown tokens.
scan :: MonadReporter r => SrcFile -> r [TokenWithPos]
scan srcFile =
  runParsecOrFail srcFile (srcFileContents srcFile) tokenListScanner
