-- | This module contains smart constructors for nodes of the Coq AST.
--   For convenience the original Coq AST is exported as well.

module Compiler.Language.Coq.AST
  ( module Language.Coq.Gallina
    -- * Comments
  , comment
    -- * Identifiers
  , ident
  , bare
  , unpackQualid
    -- * Functions
  , app
  , arrows
  , fun
    -- * Types
  , sortType
    -- * Expressions
  , string
  , equation
  , match
    -- * Imports
  , requireImportFrom
  )
where

import qualified Data.Text                     as T
import qualified Data.List.NonEmpty            as NonEmpty
import qualified Language.Coq.Gallina          as G
import           Language.Coq.Gallina

-------------------------------------------------------------------------------
-- Comments                                                                  --
-------------------------------------------------------------------------------

-- | Smart constructor for Coq comments.
comment :: String -> G.Sentence
comment = G.CommentSentence . G.Comment . T.pack

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
--   The types of the arguments are inferred by Coq.
fun :: [String] -> G.Term -> G.Term
fun args expr = G.Fun (NonEmpty.fromList binders) expr
 where
  binders :: [G.Binder]
  binders = map (G.Inferred G.Explicit . G.Ident . bare) args

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

-------------------------------------------------------------------------------
-- Imports                                                                   --
-------------------------------------------------------------------------------

-- | Creates a "From ... Require Import ..." sentence.
requireImportFrom :: G.ModuleIdent -> [G.ModuleIdent] -> G.Sentence
requireImportFrom library modules = G.ModuleSentence
  (G.Require (Just library) (Just G.Import) (NonEmpty.fromList modules))
