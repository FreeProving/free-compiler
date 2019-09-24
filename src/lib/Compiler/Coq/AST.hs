-- | This module contains smart constructors for nodes of the Coq AST.
--   For convenience the original Coq AST is exported as well.

module Compiler.Coq.AST
  ( module Language.Coq.Gallina
    -- * Comments
  , comment
    -- * Proofs.
  , blankProof
    -- * Identifiers
  , ident
  , bare
  , unpackQualid
    -- * Functions
  , app
  , arrows
  , fun
  , inferredFun
    -- * Binders
  , typedBinder
  , typedBinder'
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
  )
where

import qualified Data.List.NonEmpty            as NonEmpty
import qualified Data.Text                     as T
import           Language.Coq.Gallina
import qualified Language.Coq.Gallina          as G

-------------------------------------------------------------------------------
-- Comments                                                                  --
-------------------------------------------------------------------------------

-- | Smart constructor for Coq comments.
comment :: String -> G.Sentence
comment = G.CommentSentence . G.Comment . T.pack

-------------------------------------------------------------------------------
-- Proofs                                                                    --
-------------------------------------------------------------------------------

-- | An admitted proof that contains only a placeholder text.
blankProof :: G.Proof
blankProof = G.ProofAdmitted (T.pack "  (* FILL IN HERE *)")

-------------------------------------------------------------------------------
-- Identifiers                                                               --
-------------------------------------------------------------------------------

-- | Smart constructor for unqualified Coq identifiers.
ident :: String -> G.Ident
ident = T.pack

-- | Smart constructor for Coq identifiers.
bare :: String -> G.Qualid
bare = G.Bare . ident

-- | Gets the identifier for the given unqualified Coq identifier. Returns
--   @Nothing@ if the given identifier is qualified.
unpackQualid :: G.Qualid -> Maybe String
unpackQualid (G.Bare text    ) = Just (T.unpack text)
unpackQualid (G.Qualified _ _) = Nothing

-------------------------------------------------------------------------------
-- Functions                                                                 --
-------------------------------------------------------------------------------

-- | Smart constructor for the application of a Coq function or (type)
--   constructor.
--
--   If the first argument is an application term, the arguments are added
--   to that term. Otherwise a new application term is created.
app :: G.Term -> [G.Term] -> G.Term
app func [] = func
app (G.App func args) args' =
  G.App func (args <> NonEmpty.fromList (map G.PosArg args'))
app func args = G.App func (NonEmpty.fromList (map G.PosArg args))

-- | Smart constructor for a Coq function type.
arrows
  :: [G.Term] -- ^ The types of the function arguments.
  -> G.Term   -- ^ The return type of the function.
  -> G.Term
arrows args returnType = foldr G.Arrow returnType args

-- | Smart constructor for the construction of a Coq lambda expression with
--   the given arguments and right hand side.
--
--   The second argument contains the types of the arguments are inferred by Coq.
fun :: [String] -> [Maybe G.Term] -> G.Term -> G.Term
fun args argTypes expr = G.Fun (NonEmpty.fromList binders) expr
 where
  argNames :: [G.Name]
  argNames = map (G.Ident . bare) args

  binders :: [G.Binder]
  binders = zipWith makeBinder argTypes (argNames)

  makeBinder :: Maybe G.Term -> G.Name -> G.Binder
  makeBinder Nothing  = G.Inferred G.Explicit
  makeBinder (Just t) = flip (G.Typed G.Ungeneralizable G.Explicit) t . return

-- | Like 'fun', but all argument types are inferred.
inferredFun :: [String] -> G.Term -> G.Term
inferredFun = flip fun (repeat Nothing)

-------------------------------------------------------------------------------
-- Binders                                                                   --
-------------------------------------------------------------------------------

-- | Smart constructor for an explicit or implicit typed Coq binder.
typedBinder :: G.Explicitness -> [G.Qualid] -> G.Term -> G.Binder
typedBinder explicitness =
  G.Typed G.Ungeneralizable explicitness . NonEmpty.fromList . map G.Ident

-- | Like 'typedBinder' but for a single identifier.
typedBinder' :: G.Explicitness -> G.Qualid -> G.Term -> G.Binder
typedBinder' = flip (flip typedBinder . (: []))

-------------------------------------------------------------------------------
-- Definition sentences                                                      --
-------------------------------------------------------------------------------

-- | Smart constructor for a Coq definition sentence.
definitionSentence
  :: G.Qualid     -- ^ The name of the definition.
  -> [G.Binder]   -- ^ Binders for the parameters of the definition.
  -> Maybe G.Term -- ^ The return type of the definition.
  -> G.Term       -- ^ The right hand side of the definition.
  -> G.Sentence
definitionSentence qualid binders returnType term =
  (G.DefinitionSentence
    (G.DefinitionDef G.Global qualid binders returnType term)
  )

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------

-- | The type of a type variable.
sortType :: G.Term
sortType = G.Sort G.Type

-------------------------------------------------------------------------------
-- Expressions                                                                   --
-------------------------------------------------------------------------------

-- | Smart constructor for Coq string literals.
string :: String -> G.Term
string = G.String . T.pack

-- | Smart constructor for Coq equations for @match@ expressions.
equation :: G.Pattern -> G.Term -> G.Equation
equation = G.Equation . return . G.MultPattern . return

-- | Smart constructor for a Coq @match@ expression.
match :: G.Term -> [G.Equation] -> G.Term
match value eqns = G.Match (return item) Nothing eqns
 where
  item :: G.MatchItem
  item = G.MatchItem value Nothing Nothing

-- | Smart constructor for reflexive equality in Coq.
equals :: G.Term -> G.Term -> G.Term
equals t1 t2 = app (G.Qualid (bare "op_=__")) [t1, t2]

-- | Smart constructor for reflexive inequality in Coq.
notEquals :: G.Term -> G.Term -> G.Term
notEquals t1 t2 = app (G.Qualid (bare "op_<>__")) [t1, t2]

-- | Smart constructor for a conjunction in Coq.
conj :: G.Term -> G.Term -> G.Term
conj t1 t2 = app (G.Qualid (bare "op_/\\__")) [t1, t2]

-- | Smart constructor for a disjunction in Coq.
disj :: G.Term -> G.Term -> G.Term
disj t1 t2 = app (G.Qualid (bare "op_\\/__")) [t1, t2]

-------------------------------------------------------------------------------
-- Imports                                                                   --
-------------------------------------------------------------------------------

-- | Creates a "From ... Require Import ..." sentence.
requireImportFrom :: G.ModuleIdent -> [G.ModuleIdent] -> G.Sentence
requireImportFrom library modules = G.ModuleSentence
  (G.Require (Just library) (Just G.Import) (NonEmpty.fromList modules))
