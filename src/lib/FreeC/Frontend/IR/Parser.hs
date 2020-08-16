-- | This module contains a parser for our intermediate representation (IR).
--
--   The intermediate language is usually not parsed directly. It is more
--   common for another language (e.g., Haskell) to be parsed and converted
--   to out intermediate language. The main purpose of the IR parser is to
--   easily construct AST nodes in unit tests without making the tests
--   dependent on some front end for the construction of the AST.
--
--   The syntax of the intermediate language is based on Haskell. However,
--   there is only very little syntactic sugar. For example, there are no
--   infix operations, all applications are written in prefix notation.
--   Since the unary minus is actually syntactic sugar for @negate@ in Haskell,
--   there is also no unary minus in the intermediate representation.
--   Furthermore, the intermediate language does not implement Haskell's
--   layout rule.
--
--   The parser does not support source spans at the moment, all generated
--   nodes are annotated with 'NoSrcSpan'.
module FreeC.Frontend.IR.Parser ( Parseable(..), parseIR ) where

import           Data.List                 ( intercalate )
import           Text.Parsec               ( (<|>), Parsec )
import qualified Text.Parsec               as Parsec

import           FreeC.Frontend.IR.Scanner
import           FreeC.Frontend.IR.Token
import           FreeC.IR.SrcSpan
import qualified FreeC.IR.Syntax           as IR
import           FreeC.Monad.Reporter
import           FreeC.Pretty
import           FreeC.Util.Parsec

-- | Type for parsers of IR nodes of type @a@.
type Parser a = Parsec [ TokenWithPos ] () a

-- | Type class for IR nodes that can be parsed.
class Parseable a where
  -- | The parser to use for IR nodes of type @a@.
  --
  --   This parser should not consume @EOF@ such that it can still be
  --   combines with other parsers. Use 'parseIR' to parse an entire
  --   input string instead.
  parseIR' :: Parser a

-- | Parses an IR node of type @a@ and reports parsing errors.
--
--   Leading white spaces and comments are ignored. The full input must
--   be consumed otherwise a fatal error is reported.
parseIR :: (Parseable a, MonadReporter r) => SrcFile -> r a
parseIR srcFile = do
  tokens <- scan srcFile
  runParsecOrFail srcFile tokens (parseIR' <* Parsec.eof)

-------------------------------------------------------------------------------
-- Tokens                                                                    --
-------------------------------------------------------------------------------
-- | Creates a parser that consumes a token if the given function returns
--   @Just@ a result and fails when @Nothing@ is returned.
tokenParser :: (Token -> Maybe a) -> Parser a
tokenParser testToken = Parsec.token (showPretty . getToken) getTokenPos
  (testToken . getToken)

-- | Creates a parser that matches exactly the given token and fails otherwise.
token :: Token -> Parser ()
token t = tokenParser (\t' -> if t == t' then Just () else Nothing)

-- | Creates a parser that accepts the given keyword.
keyword :: Keyword -> Parser ()
keyword = token . Keyword

-- | Creates a parser that wraps the given parser in curly braces (i.e., @"{"@
--   and @"}"@).
bracesParser :: Parser a -> Parser a
bracesParser = Parsec.between (token LBrace) (token RBrace)

-- | Creates a parser that wraps the given parser in parenthesis (i.e., @"("@
--   and @")"@).
parensParser :: Parser a -> Parser a
parensParser = Parsec.between (token LParen) (token RParen)

-------------------------------------------------------------------------------
-- Identifiers                                                               --
-------------------------------------------------------------------------------
-- | Parser for IR identifiers.
--
--   > id ::= <varid>
--   >      | <conid>
identParser :: Parser String
identParser = varIdentToken <|> conIdentToken

-- | Parser for IR variable identifier tokens (see 'VarIdent').
--
--   > <varid> ::= (<lower> | "_") { <identletter> }
varIdentToken :: Parser String
varIdentToken = tokenParser
  $ \t -> case t of
    VarIdent ident -> Just ident
    _ -> Nothing

-- | Parser for IR constructor identifier tokens (see 'ConIdent').
--
--   > <conid> ::= <upper> { <identletter> }
conIdentToken :: Parser String
conIdentToken = tokenParser
  $ \t -> case t of
    ConIdent ident -> Just ident
    _ -> Nothing

-------------------------------------------------------------------------------
-- Symbols                                                                   --
-------------------------------------------------------------------------------
-- | Parser for IR symbols.
--
--   > sym ::= <varsym>
--   >       | <consym>
symbolParser :: Parser String
symbolParser = varSymbolToken <|> conSymbolToken

-- | Parser for IR variable symbol tokens (see 'VarSymbol').
--
--   > <varsym> ::= "(" (<namesymbol> \ <consymstart>) { <namesymbol> } ")"
varSymbolToken :: Parser String
varSymbolToken = tokenParser
  $ \t -> case t of
    VarSymbol sym -> Just sym
    _ -> Nothing

-- | Parser for IR constructor symbol tokens (see 'ConSymbol').
--
--   > <consym> ::= "(" [ <consymstart> { <namesymbol> } ] ")"
conSymbolToken :: Parser String
conSymbolToken = tokenParser
  $ \t -> case t of
    ConSymbol sym -> Just sym
    _ -> Nothing

-------------------------------------------------------------------------------
-- Module names                                                              --
-------------------------------------------------------------------------------
-- | Parser for IR module names.
--
--   > modid ::= { <conid> "." } <conid>
modNameParser :: Parser IR.ModName
modNameParser = intercalate "." <$> (conIdentToken `Parsec.sepBy1` token Dot)

-- | Like 'modNameParser' but with a trailing @"."@.
--
--   > modid' ::= <conid> "." [ modid' ]
modNameParser' :: Parser IR.ModName
modNameParser' = extendModName <$> conIdentToken <* token Dot
  <*> Parsec.optionMaybe (Parsec.try modNameParser')
 where
   extendModName :: String -> Maybe IR.ModName -> IR.ModName
   extendModName conid Nothing      = conid
   extendModName conid (Just modid) = conid ++ '.' : modid

-------------------------------------------------------------------------------
-- Names                                                                     --
-------------------------------------------------------------------------------
-- | Parser for IR names.
--
--   > name ::= id
--   >        | sym
nameParser :: Parser IR.Name
nameParser = IR.Ident <$> identParser <|> IR.Symbol <$> symbolParser

-- | Parser for IR variable names.
--
--   > varName ::= <varid>
--   >           | <varsym>
varNameParser :: Parser IR.Name
varNameParser = IR.Ident <$> varIdentToken <|> IR.Symbol <$> varSymbolToken

-- | Parser for IR constructor names.
--
--   > conName ::= <conid>
--   >           | <consym>
conNameParser :: Parser IR.Name
conNameParser = IR.Ident <$> conIdentToken <|> IR.Symbol <$> conSymbolToken

-- | Names can be parsed.
instance Parseable IR.Name where
  parseIR' = nameParser

-------------------------------------------------------------------------------
-- Quantifiable names                                                        --
-------------------------------------------------------------------------------
-- | Converts a parser that accepts unqualified names to a parser that
--   accepts optionally qualified names.
mkQualifiable :: Parser IR.Name -> Parser IR.QName
mkQualifiable p = Parsec.try qualParser <|> unQualParser
 where
   qualParser, unQualParser :: Parser IR.QName
   qualParser = IR.Qual <$> modNameParser' <*> p

   unQualParser = IR.UnQual <$> p

-- | Parser for qualifiable IR names.
--
--   > qName ::= [ modid' ] name
qNameParser :: Parser IR.QName
qNameParser = mkQualifiable nameParser

-- | Parser for qualifiable IR variable names.
--
--   > varQName ::= [ modid' ] varName
varQNameParser :: Parser IR.QName
varQNameParser = mkQualifiable varNameParser

-- | Parser for qualifiable IR constructor names.
--
--   > conQName ::= [ modid' ] conName
conQNameParser :: Parser IR.QName
conQNameParser = mkQualifiable conNameParser

-- | Qualifiable names can be parsed.
instance Parseable IR.QName where
  parseIR' = qNameParser

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------
-- | Parser for IR modules.
--
--   > module ::= "module" modid "where" { topLevel ";" } [ topLevel ]
--
--   Since IR does not support Haskell's layout rule, all top-level
--   declarations must be explicitly separated by a semicolon @";"@.
--   The last semicolon in a module is optional.
moduleParser :: Parser IR.Module
moduleParser = do
  modName <- keyword MODULE *> modNameParser <* keyword WHERE
  let ast = IR.Module
        { IR.modSrcSpan   = NoSrcSpan
        , IR.modName      = modName
        , IR.modImports   = []
        , IR.modTypeDecls = []
        , IR.modTypeSigs  = []
        , IR.modPragmas   = []
        , IR.modFuncDecls = []
        }
  topLevelDecls <- topLevelDeclParser `Parsec.sepEndBy` token Semi
  return (foldr ($) ast topLevelDecls)

-- | Parser for IR declarations that can occur at top-level in a module.
--
--   > topLevel ::= importDecl
--   >            | typeDecl
--   >            | funcDecl
--   >            | typeSig
--
--   Since all top-level declaration nodes are of different types, we
--   cannot simply return a top-level declaration. Instead, we return
--   a function that inserts the top-level declaration into the module
--   appropriately.
--
--   Function declarations must be parsed before type signatures such that
--   nullary function declarations whose return type is annotated are not
--   confused with type signatures.
topLevelDeclParser :: Parser (IR.Module -> IR.Module)
topLevelDeclParser = Parsec.choice
  [ insertImportDecl <$> importDeclParser
  , insertTypeDecl <$> typeDeclParser
  , Parsec.try (insertFuncDecl <$> funcDeclParser)
  , insertTypeSig <$> typeSigParser
  ]
 where
   -- | Inserts an import declaration into the given module.
   insertImportDecl :: IR.ImportDecl -> IR.Module -> IR.Module
   insertImportDecl importDecl ast
     = ast { IR.modImports = importDecl : IR.modImports ast }

   -- | Inserts a type declaration into the given module.
   insertTypeDecl :: IR.TypeDecl -> IR.Module -> IR.Module
   insertTypeDecl typeDecl ast
     = ast { IR.modTypeDecls = typeDecl : IR.modTypeDecls ast }

   -- | Inserts a type signature into the given module.
   insertTypeSig :: IR.TypeSig -> IR.Module -> IR.Module
   insertTypeSig typeSig ast
     = ast { IR.modTypeSigs = typeSig : IR.modTypeSigs ast }

   -- | Inserts a function declaration into the given module.
   insertFuncDecl :: IR.FuncDecl -> IR.Module -> IR.Module
   insertFuncDecl funcDecl ast
     = ast { IR.modFuncDecls = funcDecl : IR.modFuncDecls ast }

-- | Modules can be parsed.
instance Parseable IR.Module where
  parseIR' = moduleParser

-------------------------------------------------------------------------------
-- Imports                                                                   --
-------------------------------------------------------------------------------
-- | Parser for IR import declarations.
--
--   > import ::= "import" modid
importDeclParser :: Parser IR.ImportDecl
importDeclParser = IR.ImportDecl NoSrcSpan <$ keyword IMPORT <*> modNameParser

-- | Import declarations can be parsed.
instance Parseable IR.ImportDecl where
  parseIR' = importDeclParser

-------------------------------------------------------------------------------
-- Type arguments                                                            --
-------------------------------------------------------------------------------
-- | Parser for IR type variable declarations.
--
--   > typeVarDecl ::= <varid>
typeVarDeclParser :: Parser IR.TypeVarDecl
typeVarDeclParser = IR.TypeVarDecl NoSrcSpan <$> varIdentToken

-------------------------------------------------------------------------------
-- Type declarations                                                         --
-------------------------------------------------------------------------------
-- | Parser for type-level IR declarations.
--
--   > typeDecl ::= typeSynDecl
--   >            | dataDecl
typeDeclParser :: Parser IR.TypeDecl
typeDeclParser = typeSynDeclParser <|> dataDeclParser

-- | Data type and type synonym declarations can be parsed.
instance Parseable IR.TypeDecl where
  parseIR' = typeDeclParser

-------------------------------------------------------------------------------
-- Type synonym declarations                                                 --
-------------------------------------------------------------------------------
-- | Parser for IR type synonym declarations.
--
--   > typeSynDecl ::= "type" conQName { typeVarDecl } "=" type
typeSynDeclParser :: Parser IR.TypeDecl
typeSynDeclParser = IR.TypeSynDecl NoSrcSpan
  <$> (keyword TYPE *> (IR.DeclIdent NoSrcSpan <$> conQNameParser))
  <*> Parsec.many typeVarDeclParser
  <* token Equals
  <*> typeParser

-------------------------------------------------------------------------------
-- Data type declarations                                                    --
-------------------------------------------------------------------------------
-- | Parser for IR data type declarations.
--
--   > dataDecl ::= "data" conQName { typeVarDecl }
--   >              [ "=" conDecl { "|" conDecl } ]
dataDeclParser :: Parser IR.TypeDecl
dataDeclParser = IR.DataDecl NoSrcSpan
  <$> (keyword DATA *> (IR.DeclIdent NoSrcSpan <$> conQNameParser))
  <*> Parsec.many typeVarDeclParser
  <*> Parsec.option []
  (token Equals *> (conDeclParser `Parsec.sepBy1` token Pipe))

-------------------------------------------------------------------------------
-- Constructor declarations                                                  --
-------------------------------------------------------------------------------
-- | Parser for IR constructor declarations.
--
--   > conDecl ::= conQName { atype }
conDeclParser :: Parser IR.ConDecl
conDeclParser = IR.ConDecl NoSrcSpan
  <$> (IR.DeclIdent NoSrcSpan <$> conQNameParser)
  <*> Parsec.many aTypeParser

-------------------------------------------------------------------------------
-- Type signatures                                                           --
-------------------------------------------------------------------------------
-- | Parser for IR type signatures.
--
--   > varQName { "," varQName } "::" typeScheme
typeSigParser :: Parser IR.TypeSig
typeSigParser = IR.TypeSig NoSrcSpan
  <$> ((IR.DeclIdent NoSrcSpan <$> varQNameParser) `Parsec.sepBy` token Comma)
  <* token DoubleColon
  <*> typeSchemeParser

instance Parseable IR.TypeSig where
  parseIR' = typeSigParser

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------
-- | Parser for IR function declarations.
--
--   > funcDecl ::= varQName { "@" typeVarDecl } { varPat } [ "::" type ]
--   >              "=" expr
funcDeclParser :: Parser IR.FuncDecl
funcDeclParser = IR.FuncDecl NoSrcSpan
  <$> (IR.DeclIdent NoSrcSpan <$> varQNameParser)
  <*> Parsec.many (token At *> typeVarDeclParser)
  <*> Parsec.many varPatParser
  <*> Parsec.optionMaybe (token DoubleColon *> typeParser)
  <* token Equals
  <*> exprParser

-- | Function declarations can be parsed.
instance Parseable IR.FuncDecl where
  parseIR' = funcDeclParser

-------------------------------------------------------------------------------
-- Type schemes                                                          --
-------------------------------------------------------------------------------
-- | Parser for IR type schemes.
--
--   > typeScheme ::= [ "forall" { typeVarDecl } "." ] type
typeSchemeParser :: Parser IR.TypeScheme
typeSchemeParser = IR.TypeScheme NoSrcSpan
  <$> Parsec.option []
  (keyword FORALL *> Parsec.many typeVarDeclParser <* token Dot)
  <*> typeParser

-- | Parser for IR type schemes.
instance Parseable IR.TypeScheme where
  parseIR' = typeSchemeParser

-------------------------------------------------------------------------------
-- Type expressions                                                          --
-------------------------------------------------------------------------------
-- | Parser for IR type expressions.
--
--   > type  ::= btype [ "->" type ]          (function type)
typeParser :: Parser IR.Type
typeParser = IR.funcType NoSrcSpan
  <$> Parsec.many (Parsec.try (bTypeParser <* token RArrow))
  <*> bTypeParser

-- | Parser for IR type applications.
--
--   > btype ::= [ btype ] atype              (type application)
bTypeParser :: Parser IR.Type
bTypeParser = IR.typeApp NoSrcSpan <$> aTypeParser <*> Parsec.many aTypeParser

-- | Parser for IR type expressions with the highest precedence.
--
--   > atype ::= <varid>                      (type variable)
--   >         | conName                      (type constructor)
--   >         | "(" type ")"                 (parenthesized type)
aTypeParser :: Parser IR.Type
aTypeParser = typeVarParser <|> typeConParser <|> parensParser typeParser
 where
   -- @atype ::= <varid> | …@
   typeVarParser :: Parser IR.Type
   typeVarParser = IR.TypeVar NoSrcSpan <$> varIdentToken

   -- @atype ::= conName | …@
   typeConParser :: Parser IR.Type
   typeConParser = IR.TypeCon NoSrcSpan <$> conQNameParser

-- | Type expressions can be parsed.
instance Parseable IR.Type where
  parseIR' = typeParser

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------
-- | Parser for IR expressions with optional type annotation.
--
--   > expr ::= lexpr [ "::" typeScheme ]           (optional type annotation)
exprParser :: Parser IR.Expr
exprParser = setExprType <$> lExprParser
  <*> Parsec.optionMaybe (token DoubleColon *> typeSchemeParser)
 where
   -- | Sets the 'IR.exprTypeScheme' field of the given expression if it is not
   --   set already.
   --
   --   The field is usually set to @Nothing@ but can be a @Just@ value if
   --   the parsed expression was in parenthesis.
   setExprType :: IR.Expr -> Maybe IR.TypeScheme -> IR.Expr
   setExprType expr Nothing = expr
   setExprType expr (Just exprTypeScheme)
     = expr { IR.exprTypeScheme = Just exprTypeScheme }

-- | Parser for IR expressions without type annotation.
--
--   > lexpr ::= "\" varPat { varPat } "->" expr       (lambda abstraction)
--   >         | "if" expr "then" expr "else" expr     (conditional)
--   >         | "case" expr "of" alts                 (case expression)
--   >         | "let" binds "in" expr                 (let expression)
--   >         | fexpr                                 (function application)
lExprParser :: Parser IR.Expr
lExprParser = lambdaExprParser
  <|> ifExprParser
  <|> caseExprParser
  <|> letExprParser
  <|> fExprParser
 where
   -- @lexpr ::= "\\" varPat { varPat } "->" expr | …@
   lambdaExprParser :: Parser IR.Expr
   lambdaExprParser = IR.Lambda NoSrcSpan <$ token Lambda
     <*> Parsec.many1 varPatParser
     <* token RArrow
     <*> exprParser
     <*> return Nothing

   -- @lexpr ::= "if" expr "then" expr "else" expr | …@
   ifExprParser :: Parser IR.Expr
   ifExprParser = IR.If NoSrcSpan <$ keyword IF <*> exprParser <* keyword THEN
     <*> exprParser
     <* keyword ELSE
     <*> exprParser
     <*> return Nothing

   -- @lexpr ::= "case" expr "of" alts | …@
   caseExprParser :: Parser IR.Expr
   caseExprParser = IR.Case NoSrcSpan <$ keyword CASE <*> exprParser
     <* keyword OF
     <*> altsParser
     <*> return Nothing

   -- @lexpr ::= "let" binds "in" expr | …@
   letExprParser :: Parser IR.Expr
   letExprParser = IR.Let NoSrcSpan <$ keyword LET <*> bindsParser
     <* keyword IN
     <*> exprParser
     <*> return Nothing

-- | Parser for IR function application expressions.
--
--   > fexpr ::= vexpr { aexpr }                       (function application)
fExprParser :: Parser IR.Expr
fExprParser = IR.app NoSrcSpan <$> vExprParser <*> Parsec.many aExprParser

-- | Parser for IR expressions with optional visible type applications.
--
--   > vexpr ::= uexpr { varg }                   (visible type application)
--   >         | "error" [ varg ] <string>        (error term)
--   >         | wexpr                            (non-visibly applicable)
--   > varg  ::= "@" atype                        (visible type argument)
vExprParser :: Parser IR.Expr
vExprParser = visibleTypeAppParser <|> errorParser <|> wExprParser
 where
   -- @varg  ::= "@" atype@
   vArgParser :: Parser IR.Type
   vArgParser = token At *> aTypeParser

   -- @vexpr ::= uexpr { varg } | …@
   visibleTypeAppParser :: Parser IR.Expr
   visibleTypeAppParser
     = IR.visibleTypeApp NoSrcSpan <$> uExprParser <*> Parsec.many vArgParser

   -- @vexpr ::= "error" [ varg ] <string> | …@
   errorParser :: Parser IR.Expr
   errorParser = flip (IR.visibleTypeApp NoSrcSpan) <$ keyword ERROR
     <*> Parsec.option [] (return <$> vArgParser)
     <*> (IR.ErrorExpr NoSrcSpan <$> stringToken <*> return Nothing)

-- | Parser for IR expressions that can be applied to their type arguments.
--
--   > uexpr ::= varQName                            (variable)
--   >         | conQName                            (constructor)
--   >         | "undefined"                         (error term)
--
--   Visible type applications can also occur in @error@ expressions,
--   but the type argument is written between @error@ and the error
--   message. Thus, they have to be handled separately by @vexpr@.
uExprParser :: Parser IR.Expr
uExprParser = varExprParser <|> conExprParser <|> undefinedParser
 where
   -- @uexpr ::= varQName | …@
   varExprParser :: Parser IR.Expr
   varExprParser = IR.Var NoSrcSpan <$> varQNameParser <*> return Nothing

   -- @uexpr ::= conQName | …@
   conExprParser :: Parser IR.Expr
   conExprParser = IR.Con NoSrcSpan <$> conQNameParser <*> return Nothing

   -- @uexpr ::= "undefined" | …@
   undefinedParser :: Parser IR.Expr
   undefinedParser
     = IR.Undefined NoSrcSpan <$ keyword UNDEFINED <*> return Nothing

-- | Parser for IR expressions that cannot be applied to type arguments.
--
--   > wexpr ::= literal                             (literal)
--   >         | "(" expr ")"                        (parenthesized expression)
wExprParser :: Parser IR.Expr
wExprParser = literalParser <|> parensParser exprParser

-- | Parser for IR expressions with the highest precedence.
--
--   > aexpr ::= uexpr                               (non-visibly applied)
--   >         | wexpr                               (non-visibly applicable)
aExprParser :: Parser IR.Expr
aExprParser = uExprParser <|> wExprParser

-- | Expressions can be parsed.
instance Parseable IR.Expr where
  parseIR' = exprParser

-------------------------------------------------------------------------------
-- @case@ expression alternatives                                            --
-------------------------------------------------------------------------------
-- | Parser for zero or more IR @case@ expression alternatives.
--
--   > alts ::= "{" [ alt { ";" alt } ] "}"
altsParser :: Parser [ IR.Alt ]
altsParser = bracesParser (altParser `Parsec.sepEndBy` token Semi)

-- | Parser for IR @case@ expression alternatives.
--
--   > alt ::= conPat { varPat } "->" expr
altParser :: Parser IR.Alt
altParser = IR.Alt NoSrcSpan <$> conPatParser <*> Parsec.many varPatParser
  <* token RArrow
  <*> exprParser

-------------------------------------------------------------------------------
-- @let@ expression bindings                                            --
-------------------------------------------------------------------------------
-- | Parser for zero or more IR @let@ bindings.
--
--   > binds ::= "{" [ bind { ";" bind } ] "}"
bindsParser :: Parser [ IR.Bind ]
bindsParser = bracesParser (bindParser `Parsec.sepEndBy` token Semi)

-- | Parser for IR @case@ expression alternatives.
--
--   > bind ::= varPat "=" expr
bindParser :: Parser IR.Bind
bindParser = IR.Bind NoSrcSpan <$> varPatParser <* token Equals <*> exprParser

-------------------------------------------------------------------------------
-- Patterns                                                                  --
-------------------------------------------------------------------------------
-- | Parser for IR constructor patterns.
--
--   > conPat ::= conQName
conPatParser :: Parser IR.ConPat
conPatParser = IR.ConPat NoSrcSpan <$> conQNameParser

-- | Parser for IR variable patterns with optional type annotation and @!@.
--
--   > varPat ::= ["!"] "(" <varid> "::" type ")"
--   >          | ["!"] <varid>
varPatParser :: Parser IR.VarPat
varPatParser = token Bang
  *> (typedVarPatParser True <|> untypedVarPatParser True)
  <|> typedVarPatParser False
  <|> untypedVarPatParser False
 where
   -- @varPat ::= ["!"] "(" <varid> "::" type ")" | …@
   typedVarPatParser :: Bool -> Parser IR.VarPat
   typedVarPatParser isStrict = parensParser
     (IR.VarPat NoSrcSpan <$> varIdentToken <* token DoubleColon
      <*> (Just <$> typeParser)
      <*> return isStrict)

   -- @varPat ::= ["!"] <varid> | …@
   untypedVarPatParser :: Bool -> Parser IR.VarPat
   untypedVarPatParser isStrict = IR.VarPat NoSrcSpan <$> varIdentToken
     <*> return Nothing
     <*> return isStrict

-------------------------------------------------------------------------------
-- Literals                                                                  --
-------------------------------------------------------------------------------
-- | Parser for IR literals.
--
--   > literal ::= <integer>
--
--   At the moment there are only integer literals.
--   Even though there are string literals, they are only used
--   in @error@ terms.
literalParser :: Parser IR.Expr
literalParser = IR.IntLiteral NoSrcSpan <$> integerToken <*> return Nothing

-- | Parser for an integer literal token (see 'IntToken').
--
--   > <integer>   ::= [ "+" | "-" ] <natural>
--   > <natural>   ::= <decimal>
--   >               | "0o" <octal>       | "0O" <octal>
--   >               | "0x" <hexadecimal> | "0X" <hexadecimal>
integerToken :: Parser Integer
integerToken = tokenParser
  $ \t -> case t of
    IntToken value -> Just value
    _ -> Nothing

-- | Parser for a string literal token (see 'StrToken').
--
--   > <string> ::= '"' … '"'                        (any valid Haskell string)
stringToken :: Parser String
stringToken = tokenParser
  $ \t -> case t of
    StrToken value -> Just value
    _ -> Nothing
