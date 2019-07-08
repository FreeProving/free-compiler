-- | This module contains smart constructors for nodes of the Coq AST.
--   For convenience the original Coq AST is exported as well.

module Compiler.Language.Coq.AST
  ( module Language.Coq.Gallina
  , bare
  , unpackQualid
  , app
  , arrows
  , sortType
  )
where

import qualified Data.Text                     as T
import qualified Language.Coq.Gallina          as G
import           Language.Coq.Gallina

import           Compiler.Util.Data.List.NonEmpty

-------------------------------------------------------------------------------
-- Identifiers                                                               --
-------------------------------------------------------------------------------

-- | Smart constructor for Coq identifiers.
bare :: String -> G.Qualid
bare = G.Bare . T.pack

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
app (G.App func args) args' =
  G.App func (args <> toNonEmptyList (map G.PosArg args'))
app func args = G.App func (toNonEmptyList (map G.PosArg args))

-- | Smart constructor for a Coq function type.
arrows
  :: [G.Term] -- ^ The types of the function arguments.
  -> G.Term   -- ^ The return type of the function.
  -> G.Term
arrows args returnType = foldr G.Arrow returnType args

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------

-- | The type of a type variable.
sortType :: G.Term
sortType = G.Sort G.Type
