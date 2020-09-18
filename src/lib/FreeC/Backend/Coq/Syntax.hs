-- | This module contains smart constructors for nodes of the Coq AST.
--   For convenience the original Coq AST is exported as well.
module FreeC.Backend.Coq.Syntax
  ( module Language.Coq.Gallina
    -- * Comments
  , comment
  , commentedSentences
  , unpackComment
    -- * Proofs
  , blankProof
    -- * Identifiers
  , ident
  , bare
  , unpackQualid
  , access
    -- * Functions
  , app
  , explicitApp
  , arrows
  , fun
  , inferredFun
    -- * Binders
  , typedBinder
  , typedBinder'
    -- * Assumptions
  , variable
    -- * Definition Sentences
  , definitionSentence
    -- * Notation sentences
  , notationSentence
  , nSymbol
  , nIdent
  , sModLevel
  , sModIdentLevel
    -- * Types
  , sortType
    -- * Expressions
  , string
  , equation
  , match
  , equals
  , notEquals
  , conj
  , disj
  , forall
    -- * Imports
  , requireImportFrom
  , requireExportFrom
  , requireFrom
  , moduleImport
  , moduleExport
  ) where

import           Prelude              hiding ( Num )

import           Data.Composition     ( (.:) )
import qualified Data.List.NonEmpty   as NonEmpty
import qualified Data.Text            as Text
import           Language.Coq.Gallina

-------------------------------------------------------------------------------
-- Comments                                                                  --
-------------------------------------------------------------------------------
-- | Smart constructor for Coq comments.
comment :: String -> Sentence
comment = CommentSentence . Comment . Text.pack

-- | Puts a comment in front of the sentences if there is any sentence.
commentedSentences :: String -> [Sentence] -> [Sentence]
commentedSentences _ []          = []
commentedSentences str sentences = comment str : sentences

-- | Gets the string from theCoq  comment.
unpackComment :: Comment -> String
unpackComment (Comment c) = Text.unpack c

-------------------------------------------------------------------------------
-- Proofs                                                                    --
-------------------------------------------------------------------------------
-- | An admitted proof that contains only a placeholder text.
blankProof :: Proof
blankProof = ProofAdmitted (Text.pack "  (* FILL IN HERE *)")

-------------------------------------------------------------------------------
-- Identifiers                                                               --
-------------------------------------------------------------------------------
-- | Smart constructor for unqualified Coq identifiers.
ident :: String -> Ident
ident = Text.pack

-- | Smart constructor for Coq identifiers.
bare :: String -> Qualid
bare = Bare . ident

-- | Gets the identifier for the given unqualified Coq identifier. Returns
--   @Nothing@ if the given identifier is qualified.
unpackQualid :: Qualid -> Maybe String
unpackQualid (Bare text)     = Just (Text.unpack text)
unpackQualid (Qualified _ _) = Nothing

-- | Smart constructor for combining a module name and an identifier.
access :: ModuleIdent -> Ident -> Ident
access modName name = Text.append modName (Text.cons '.' name)

-------------------------------------------------------------------------------
-- Functions                                                                 --
-------------------------------------------------------------------------------
-- | Smart constructor for the application of a Coq function or (type)
--   constructor.
--
--   If the first argument is an application term, the arguments are added
--   to that term. Otherwise a new application term is created.
app :: Term -> [Term] -> Term
app func []               = func
app (App func args) args' = App func
  (args <> NonEmpty.fromList (map PosArg args'))
app func args             = App func (NonEmpty.fromList (map PosArg args))

-- | Smart constructor for the explicit application of a Coq function or
--   constructor to otherwise inferred type arguments.
--
--   If there are no type arguments, no 'ExplicitApp' will be created.
explicitApp :: Qualid -> [Term] -> Term
explicitApp qualid []       = Qualid qualid
explicitApp qualid typeArgs = ExplicitApp qualid typeArgs

-- | Smart constructor for a Coq function type.
arrows :: [Term] -- ^ The types of the function arguments.
       -> Term   -- ^ The return type of the function.
       -> Term
arrows args returnType = foldr Arrow returnType args

-- | Smart constructor for the construction of a Coq lambda expression with
--   the given arguments and right-hand side.
--
--   The second argument contains the types of the arguments are inferred
--   by Coq.
fun :: [Qualid] -> [Maybe Term] -> Term -> Term
fun args argTypes = Fun (NonEmpty.fromList binders)
 where
  argNames :: [Name]
  argNames = map Ident args

  binders :: [Binder]
  binders = zipWith makeBinder argTypes argNames

  makeBinder :: Maybe Term -> Name -> Binder
  makeBinder Nothing  = Inferred Explicit
  makeBinder (Just t) = flip (Typed Ungeneralizable Explicit) t . return

-- | Like 'fun', but all argument types are inferred.
inferredFun :: [Qualid] -> Term -> Term
inferredFun = flip fun (repeat Nothing)

-------------------------------------------------------------------------------
-- Binders                                                                   --
-------------------------------------------------------------------------------
-- | Smart constructor for an explicit or implicit typed Coq binder.
typedBinder :: Generalizability -> Explicitness -> [Qualid] -> Term -> Binder
typedBinder generalizability explicitness
  = Typed generalizability explicitness . NonEmpty.fromList . map Ident

-- | Like 'typedBinder' but for a single identifier.
typedBinder' :: Generalizability -> Explicitness -> Qualid -> Term -> Binder
typedBinder' generalizability explicitness term
  = typedBinder generalizability explicitness [term]

-------------------------------------------------------------------------------
-- Assumptions                                                               --
-------------------------------------------------------------------------------
-- | Generates a @Variable@ assumption sentence.
variable :: [Qualid] -> Term -> Sentence
variable
  = AssumptionSentence . Assumption Variable .: Assums . NonEmpty.fromList

-------------------------------------------------------------------------------
-- Definition Sentences                                                      --
-------------------------------------------------------------------------------
-- | Smart constructor for a Coq definition sentence.
definitionSentence
  :: Qualid     -- ^ The name of the definition.
  -> [Binder]   -- ^ Binders for the parameters of the definition.
  -> Maybe Term -- ^ The return type of the definition.
  -> Term       -- ^ The right-hand side of the definition.
  -> Sentence
definitionSentence qualid binders returnType term = DefinitionSentence
  (DefinitionDef Global qualid binders returnType term)

-------------------------------------------------------------------------------
-- Definition sentences                                                      --
-------------------------------------------------------------------------------
-- | Smart constructor for a Coq notation sentence.
notationSentence
  :: NonEmpty.NonEmpty NotationToken -- ^ The notation to define.
  -> Term                            -- ^ The right-hand side of the notation.
  -> [SyntaxModifier]                -- ^ The syntax modifiers of the notation.
  -> Sentence
notationSentence tokens rhs smods = NotationSentence
  (NotationDefinition tokens rhs smods)

-- | Smart constructor for a notation token that is a keyword of the notation.
nSymbol :: String -> NotationToken
nSymbol = NSymbol . Text.pack

-- | Smart constructor for a notation token that is a variable in the notation.
nIdent :: String -> NotationToken
nIdent = NIdent . ident

-- | Smart constructor for a parsing level syntax modifier.
sModLevel :: Num -> SyntaxModifier
sModLevel = SModLevel . Level

-- | Smart constructor for a identifier parsing level syntax modifier.
sModIdentLevel :: NonEmpty.NonEmpty String -> Maybe Num -> SyntaxModifier
sModIdentLevel idents (Just lvl) = SModIdentLevel (NonEmpty.map ident idents)
  (ExplicitLevel $ Level lvl)
sModIdentLevel idents Nothing    = SModIdentLevel (NonEmpty.map ident idents)
  NextLevel

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------
-- | The type of a type variable.
sortType :: Term
sortType = Sort Type

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------
-- | Smart constructor for Coq string literals.
string :: String -> Term
string = String . Text.pack

-- | Smart constructor for Coq equations for @match@ expressions.
equation :: Pattern -> Term -> Equation
equation = Equation . return . MultPattern . return

-- | Smart constructor for a Coq @match@ expression.
match :: Term -> [Equation] -> Term
match value = Match (return item) Nothing
 where
  item :: MatchItem
  item = MatchItem value Nothing Nothing

-- | Smart constructor for reflexive equality in Coq.
equals :: Term -> Term -> Term
equals t1 t2 = app (Qualid (bare "op_=__")) [t1, t2]

-- | Smart constructor for reflexive inequality in Coq.
notEquals :: Term -> Term -> Term
notEquals t1 t2 = app (Qualid (bare "op_<>__")) [t1, t2]

-- | Smart constructor for a conjunction in Coq.
conj :: Term -> Term -> Term
conj t1 t2 = app (Qualid (bare "op_/\\__")) [t1, t2]

-- | Smart constructor for a disjunction in Coq.
disj :: Term -> Term -> Term
disj t1 t2 = app (Qualid (bare "op_\\/__")) [t1, t2]

-- | Smart constructor for a forall term in Coq.
forall :: [Binder] -> Term -> Term
forall [] t = t
forall bs t = Forall (NonEmpty.fromList bs) t

-------------------------------------------------------------------------------
-- Imports                                                                   --
-------------------------------------------------------------------------------
-- | Creates a @From … Require Import …@ sentence.
requireImportFrom :: ModuleIdent -> [ModuleIdent] -> Sentence
requireImportFrom library modules = ModuleSentence
  (Require (Just library) (Just Import) (NonEmpty.fromList modules))

-- | Creates a @From … Require Export …@ sentence.
requireExportFrom :: ModuleIdent -> [ModuleIdent] -> Sentence
requireExportFrom library modules = ModuleSentence
  (Require (Just library) (Just Export) (NonEmpty.fromList modules))

-- | Creates a @From … Require …@ sentence.
requireFrom :: ModuleIdent -> [ModuleIdent] -> Sentence
requireFrom library modules = ModuleSentence
  (Require (Just library) Nothing (NonEmpty.fromList modules))

-- | Creates an @Import …@ sentence.
moduleImport :: [ModuleIdent] -> Sentence
moduleImport modules = ModuleSentence
  (ModuleImport Import (NonEmpty.fromList modules))

-- | Creates an @Export …@ sentence.
moduleExport :: [ModuleIdent] -> Sentence
moduleExport modules = ModuleSentence
  (ModuleImport Export (NonEmpty.fromList modules))
