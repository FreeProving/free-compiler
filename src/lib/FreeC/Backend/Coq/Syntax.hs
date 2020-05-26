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
  )
where

import           Data.Composition               ( (.:) )
import qualified Data.List.NonEmpty            as NonEmpty
import qualified Data.Text                     as Text
import           Language.Coq.Gallina
import qualified Language.Coq.Gallina          as Coq

-------------------------------------------------------------------------------
-- Comments                                                                  --
-------------------------------------------------------------------------------

-- | Smart constructor for Coq comments.
comment :: String -> Coq.Sentence
comment = Coq.CommentSentence . Coq.Comment . Text.pack

-------------------------------------------------------------------------------
-- Proofs                                                                    --
-------------------------------------------------------------------------------

-- | An admitted proof that contains only a placeholder text.
blankProof :: Coq.Proof
blankProof = Coq.ProofAdmitted (Text.pack "  (* FILL IN HERE *)")

-------------------------------------------------------------------------------
-- Identifiers                                                               --
-------------------------------------------------------------------------------

-- | Smart constructor for unqualified Coq identifiers.
ident :: String -> Coq.Ident
ident = Text.pack

-- | Smart constructor for Coq identifiers.
bare :: String -> Coq.Qualid
bare = Coq.Bare . ident

-- | Gets the identifier for the given unqualified Coq identifier. Returns
--   @Nothing@ if the given identifier is qualified.
unpackQualid :: Coq.Qualid -> Maybe String
unpackQualid (Coq.Bare text    ) = Just (Text.unpack text)
unpackQualid (Coq.Qualified _ _) = Nothing

-------------------------------------------------------------------------------
-- Functions                                                                 --
-------------------------------------------------------------------------------

-- | Smart constructor for the application of a Coq function or (type)
--   constructor.
--
--   If the first argument is an application term, the arguments are added
--   to that term. Otherwise a new application term is created.
app :: Coq.Term -> [Coq.Term] -> Coq.Term
app func [] = func
app (Coq.App func args) args' =
  Coq.App func (args <> NonEmpty.fromList (map Coq.PosArg args'))
app func args = Coq.App func (NonEmpty.fromList (map Coq.PosArg args))

-- | Smart constructor for the explicit application of a Coq function or
--   constructor to otherwise inferred type arguments.
--
--   If there are no type arguments, no 'Coq.ExplicitApp' will be created.
explicitApp :: Coq.Qualid -> [Coq.Term] -> Coq.Term
explicitApp qualid []       = Coq.Qualid qualid
explicitApp qualid typeArgs = Coq.ExplicitApp qualid typeArgs

-- | Smart constructor for a Coq function type.
arrows
  :: [Coq.Term] -- ^ The types of the function arguments.
  -> Coq.Term   -- ^ The return type of the function.
  -> Coq.Term
arrows args returnType = foldr Coq.Arrow returnType args

-- | Smart constructor for the construction of a Coq lambda expression with
--   the given arguments and right hand side.
--
--   The second argument contains the types of the arguments are inferred
--   by Coq.
fun :: [Coq.Qualid] -> [Maybe Coq.Term] -> Coq.Term -> Coq.Term
fun args argTypes = Coq.Fun (NonEmpty.fromList binders)
 where
  argNames :: [Coq.Name]
  argNames = map Coq.Ident args

  binders :: [Coq.Binder]
  binders = zipWith makeBinder argTypes argNames

  makeBinder :: Maybe Coq.Term -> Coq.Name -> Coq.Binder
  makeBinder Nothing = Coq.Inferred Coq.Explicit
  makeBinder (Just t) =
    flip (Coq.Typed Coq.Ungeneralizable Coq.Explicit) t . return

-- | Like 'fun', but all argument types are inferred.
inferredFun :: [Coq.Qualid] -> Coq.Term -> Coq.Term
inferredFun = flip fun (repeat Nothing)

-------------------------------------------------------------------------------
-- Binders                                                                   --
-------------------------------------------------------------------------------

-- | Smart constructor for an explicit or implicit typed Coq binder.
typedBinder :: Coq.Explicitness -> [Coq.Qualid] -> Coq.Term -> Coq.Binder
typedBinder explicitness =
  Coq.Typed Coq.Ungeneralizable explicitness . NonEmpty.fromList . map Coq.Ident

-- | Like 'typedBinder' but for a single identifier.
typedBinder' :: Coq.Explicitness -> Coq.Qualid -> Coq.Term -> Coq.Binder
typedBinder' = flip (flip typedBinder . (: []))

-------------------------------------------------------------------------------
-- Assumptions                                                               --
-------------------------------------------------------------------------------

-- | Generates a @Variable@ assumption sentence.
variable :: [Coq.Qualid] -> Coq.Term -> Coq.Sentence
variable =
  Coq.AssumptionSentence
    .  Coq.Assumption Coq.Variable
    .: Coq.Assums
    .  NonEmpty.fromList

-------------------------------------------------------------------------------
-- Definition sentences                                                      --
-------------------------------------------------------------------------------

-- | Smart constructor for a Coq definition sentence.
definitionSentence
  :: Coq.Qualid     -- ^ The name of the definition.
  -> [Coq.Binder]   -- ^ Binders for the parameters of the definition.
  -> Maybe Coq.Term -- ^ The return type of the definition.
  -> Coq.Term       -- ^ The right hand side of the definition.
  -> Coq.Sentence
definitionSentence qualid binders returnType term = Coq.DefinitionSentence
  (Coq.DefinitionDef Coq.Global qualid binders returnType term)

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------

-- | The type of a type variable.
sortType :: Coq.Term
sortType = Coq.Sort Coq.Type

-------------------------------------------------------------------------------
-- Expressions                                                              --
-------------------------------------------------------------------------------

-- | Smart constructor for Coq string literals.
string :: String -> Coq.Term
string = Coq.String . Text.pack

-- | Smart constructor for Coq equations for @match@ expressions.
equation :: Coq.Pattern -> Coq.Term -> Coq.Equation
equation = Coq.Equation . return . Coq.MultPattern . return

-- | Smart constructor for a Coq @match@ expression.
match :: Coq.Term -> [Coq.Equation] -> Coq.Term
match value = Coq.Match (return item) Nothing
 where
  item :: Coq.MatchItem
  item = Coq.MatchItem value Nothing Nothing

-- | Smart constructor for reflexive equality in Coq.
equals :: Coq.Term -> Coq.Term -> Coq.Term
equals t1 t2 = app (Coq.Qualid (bare "op_=__")) [t1, t2]

-- | Smart constructor for reflexive inequality in Coq.
notEquals :: Coq.Term -> Coq.Term -> Coq.Term
notEquals t1 t2 = app (Coq.Qualid (bare "op_<>__")) [t1, t2]

-- | Smart constructor for a conjunction in Coq.
conj :: Coq.Term -> Coq.Term -> Coq.Term
conj t1 t2 = app (Coq.Qualid (bare "op_/\\__")) [t1, t2]

-- | Smart constructor for a disjunction in Coq.
disj :: Coq.Term -> Coq.Term -> Coq.Term
disj t1 t2 = app (Coq.Qualid (bare "op_\\/__")) [t1, t2]

-------------------------------------------------------------------------------
-- Imports                                                                   --
-------------------------------------------------------------------------------

-- | Creates a @From ... Require Import ...@ sentence.
requireImportFrom :: Coq.ModuleIdent -> [Coq.ModuleIdent] -> Coq.Sentence
requireImportFrom library modules = Coq.ModuleSentence
  (Coq.Require (Just library) (Just Coq.Import) (NonEmpty.fromList modules))

-- | Creates a @From ... Require Export ...@ sentence.
requireExportFrom :: Coq.ModuleIdent -> [Coq.ModuleIdent] -> Coq.Sentence
requireExportFrom library modules = Coq.ModuleSentence
  (Coq.Require (Just library) (Just Coq.Export) (NonEmpty.fromList modules))
