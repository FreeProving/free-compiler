-- | This module contains auxilary functions that help to generate Coq code
--   that uses the @Free@ monad.

module Compiler.Converter.Free where

import           Data.List.NonEmpty             ( NonEmpty(..) )
import           Data.Maybe                     ( maybe )

import qualified Compiler.Coq.AST              as G
import qualified Compiler.Coq.Base             as CoqBase
import           Compiler.Environment.Fresh
import           Compiler.Monad.Converter

-------------------------------------------------------------------------------
-- Generic arguments for free monad                                          --
-------------------------------------------------------------------------------

-- | The declarations of type parameters for the @Free@ monad.
--
--   The first argument controlls whether the generated binders are explicit
--   (e.g. @(Shape : Type)@) or implicit (e.g. @{Shape : Type}@).
genericArgDecls :: G.Explicitness -> [G.Binder]
genericArgDecls explicitness =
  map (uncurry (G.typedBinder' explicitness)) CoqBase.freeArgs

-- | An explicit binder for the @Partial@ instance that is passed to partial
--   function declarations.
partialArgDecl :: G.Binder
partialArgDecl = uncurry (G.typedBinder' G.Explicit) CoqBase.partialArg

-- | Smart constructor for the application of a Coq function or (type)
--   constructor that requires the parameters for the @Free@ monad.
genericApply :: G.Qualid -> [G.Term] -> G.Term
genericApply func args = G.app (G.Qualid func) (genericArgs ++ args)
  where genericArgs = map (G.Qualid . fst) CoqBase.freeArgs

-------------------------------------------------------------------------------
-- Free monad operations                                                     --
-------------------------------------------------------------------------------

-- | Wraps the given Coq term with the @pure@ constructor of the @Free@ monad.
generatePure :: G.Term -> Converter G.Term
generatePure = return . G.app (G.Qualid CoqBase.freePureCon) . (: [])

-- | Generates a Coq expressions that binds the given value to a fresh variable.
--
--   The generated fresh variable is passed to the given function. It is not
--   visible outside of that function.
--   If the given expression is an application of the @pure@ constructor,
--   no bind will be generated. The wrapped value is passed directly to
--   the given function instead of a fresh variable.
--
--   If the second argument is @Nothing@, the type of the fresh variable is
--   inferred by Coq.
generateBind
  :: G.Term        -- ^ The left hand side of the bind operator.
  -> Maybe G.Term  -- ^ The  Coq type of the value to bind or @Nothing@ if it
                   --   should be inferred by Coq.
  -> (G.Term -> Converter G.Term)
                   -- ^ Converter for the right hand side of the generated
                   --   function. The first argument is the fresh variable.
  -> Converter G.Term
generateBind (G.App (G.Qualid con) ((G.PosArg arg) :| [])) _ generateRHS
  | con == CoqBase.freePureCon = generateRHS arg
generateBind expr' argType' generateRHS = localEnv $ do
  x   <- freshCoqIdent (suggestPrefixFor expr')
  rhs <- generateRHS (G.Qualid x)
  return (G.app (G.Qualid CoqBase.freeBind) [expr', G.fun [x] [argType'] rhs])
 where
  -- | Suggests a prefix for the fresh varibale the given expression
  --   is bound to.
  suggestPrefixFor :: G.Term -> String
  suggestPrefixFor (G.Qualid qualid) =
    maybe defaultPrefix id (G.unpackQualid qualid)
  suggestPrefixFor _ = defaultPrefix

  -- | The prefix for the fresh variable if 'suggestPrefixFor' cannot find
  --   a better prefix.
  defaultPrefix :: String
  defaultPrefix = freshArgPrefix
