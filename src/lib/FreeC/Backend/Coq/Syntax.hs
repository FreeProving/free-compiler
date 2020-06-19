-- | This module contains smart constructors for nodes of the Coq AST.
--   For convenience the original Coq AST is exported as well.

module FreeC.Backend.Coq.Syntax
  ( module Language.Coq.Gallina
    -- * Comments
  , comment
    -- * Proofs
  , blankProof
    -- * Identifiers
  , ident
  , bare
  , unpackQualid
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
  -- * Definition sentences
  , definitionSentence
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
    -- * Imports
  , requireImportFrom
  , requireExportFrom
  , requireFrom
  )
where

import           Data.Composition               ( (.:) )
import qualified Data.List.NonEmpty            as NonEmpty
import qualified Data.Text                     as Text
import           Language.Coq.Gallina

-------------------------------------------------------------------------------
-- Comments                                                                  --
-------------------------------------------------------------------------------

-- | Smart constructor for Coq comments.
comment :: String -> Sentence
comment = CommentSentence . Comment . Text.pack

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
unpackQualid (Bare text    ) = Just (Text.unpack text)
unpackQualid (Qualified _ _) = Nothing

-------------------------------------------------------------------------------
-- Functions                                                                 --
-------------------------------------------------------------------------------

-- | Smart constructor for the application of a Coq function or (type)
--   constructor.
--
--   If the first argument is an application term, the arguments are added
--   to that term. Otherwise a new application term is created.
app :: Term -> [Term] -> Term
app func [] = func
app (App func args) args' =
  App func (args <> NonEmpty.fromList (map PosArg args'))
app func args = App func (NonEmpty.fromList (map PosArg args))

-- | Smart constructor for the explicit application of a Coq function or
--   constructor to otherwise inferred type arguments.
--
--   If there are no type arguments, no 'ExplicitApp' will be created.
explicitApp :: Qualid -> [Term] -> Term
explicitApp qualid []       = Qualid qualid
explicitApp qualid typeArgs = ExplicitApp qualid typeArgs

-- | Smart constructor for a Coq function type.
arrows
  :: [Term] -- ^ The types of the function arguments.
  -> Term   -- ^ The return type of the function.
  -> Term
arrows args returnType = foldr Arrow returnType args

-- | Smart constructor for the construction of a Coq lambda expression with
--   the given arguments and right hand side.
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
typedBinder :: Explicitness -> [Qualid] -> Term -> Binder
typedBinder explicitness =
  Typed Ungeneralizable explicitness . NonEmpty.fromList . map Ident

-- | Like 'typedBinder' but for a single identifier.
typedBinder' :: Explicitness -> Qualid -> Term -> Binder
typedBinder' = flip (flip typedBinder . (: []))

-------------------------------------------------------------------------------
-- Assumptions                                                               --
-------------------------------------------------------------------------------

-- | Generates a @Variable@ assumption sentence.
variable :: [Qualid] -> Term -> Sentence
variable =
  AssumptionSentence . Assumption Variable .: Assums . NonEmpty.fromList

-------------------------------------------------------------------------------
-- Definition sentences                                                      --
-------------------------------------------------------------------------------

-- | Smart constructor for a Coq definition sentence.
definitionSentence
  :: Qualid     -- ^ The name of the definition.
  -> [Binder]   -- ^ Binders for the parameters of the definition.
  -> Maybe Term -- ^ The return type of the definition.
  -> Term       -- ^ The right hand side of the definition.
  -> Sentence
definitionSentence qualid binders returnType term =
  DefinitionSentence (DefinitionDef Global qualid binders returnType term)

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------

-- | The type of a type variable.
sortType :: Term
sortType = Sort Type

-------------------------------------------------------------------------------
-- Expressions                                                              --
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

-------------------------------------------------------------------------------
-- Imports                                                                   --
-------------------------------------------------------------------------------

-- | Creates a @From ... Require Import ...@ sentence.
requireImportFrom :: ModuleIdent -> [ModuleIdent] -> Sentence
requireImportFrom library modules = ModuleSentence
  (Require (Just library) (Just Import) (NonEmpty.fromList modules))

-- | Creates a @From ... Require Export ...@ sentence.
requireExportFrom :: ModuleIdent -> [ModuleIdent] -> Sentence
requireExportFrom library modules = ModuleSentence
  (Require (Just library) (Just Export) (NonEmpty.fromList modules))

-- | Creates a @From ... Require ...@ sentence.
requireFrom :: ModuleIdent -> [ModuleIdent] -> Sentence
requireFrom library modules = ModuleSentence
  (Require (Just library) Nothing (NonEmpty.fromList modules))
