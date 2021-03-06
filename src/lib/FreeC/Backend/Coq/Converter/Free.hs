-- | This module contains auxiliary functions that help to generate Coq code
--   that uses the @Free@ monad.
module FreeC.Backend.Coq.Converter.Free where

import           Data.List                ( elemIndex )
import           Data.List.NonEmpty       ( NonEmpty(..) )
import           Data.Maybe               ( maybe )

import qualified FreeC.Backend.Coq.Base   as Coq.Base
import qualified FreeC.Backend.Coq.Syntax as Coq
import           FreeC.Environment.Fresh
import           FreeC.Monad.Converter

-------------------------------------------------------------------------------
-- Generic Arguments for Free Monad                                          --
-------------------------------------------------------------------------------
-- | The declarations of type parameters for the @Free@ monad.
--
--   The first argument controls whether the generated binders are explicit
--   (e.g. @(Shape : Type)@) or implicit (e.g. @{Shape : Type}@).
genericArgDecls :: Coq.Explicitness -> [Coq.Binder]
genericArgDecls explicitness = map
  (uncurry (Coq.typedBinder' Coq.Ungeneralizable explicitness))
  Coq.Base.freeArgs

-- | @Variable@ sentences for the parameters of the @Free@ monad.
--
--   @Variable Shape : Type.@ and @Variable Pos : Shape -> Type.@
genericArgVariables :: [Coq.Sentence]
genericArgVariables = map (uncurry (Coq.variable . return)) Coq.Base.freeArgs

-- | Smart constructor for the application of a Coq function or (type)
--   constructor that requires the parameters for the @Free@ monad.
genericApply
  :: Coq.Qualid -- ^ The name of the function or (type) constructor
  -> [Coq.Term] -- ^ The type class instances to pass to the callee.
  -> [Coq.Term] -- ^ Implicit arguments to pass explicitly to the callee.
  -> [Coq.Term] -- ^ The actual arguments of the callee.
  -> Coq.Term
genericApply func explicitEffectArgs implicitEffectArgs = genericApply'
  (Coq.Qualid func) explicitEffectArgs [] implicitEffectArgs []

-- | Like 'genericApply' but takes a function or (type) constructor term instead
--   of a qualified identifier as its first argument.
genericApply'
  :: Coq.Term   -- ^ The function or (type) constructor term
  -> [Coq.Term] -- ^ The explicit type class instances to pass to the callee.
  -> [Coq.Term] -- ^ The implicit type class instances to pass to the callee.
  -> [Coq.Term] -- ^ Implicit arguments to pass explicitly to the callee.
  -> [Coq.Term] -- ^ The implicit type class arguments that are dependent on
                --   the implicit arguments.
  -> [Coq.Term] -- ^ The actual arguments of the callee.
  -> Coq.Term
genericApply' func explicitEffectArgs implicitEffectArgs implicitArgs
  typedEffectArgs args | null allImplicitArgs = Coq.app func allArgs
                       | otherwise = let Coq.Qualid qualid = func
                                     in Coq.explicitApp qualid allArgs
 where
  genericArgs :: [Coq.Term]
  genericArgs = map (Coq.Qualid . fst) Coq.Base.freeArgs

  allImplicitArgs :: [Coq.Term]
  allImplicitArgs = implicitEffectArgs ++ implicitArgs ++ typedEffectArgs

  allArgs :: [Coq.Term]
  allArgs = genericArgs
    ++ implicitEffectArgs
    ++ explicitEffectArgs
    ++ implicitArgs
    ++ typedEffectArgs
    ++ args

-- | Smart constructor for a @ForFree@ statement with a given type, property
--   and @Free@ value.
genericForFree :: Coq.Term -> Coq.Qualid -> Coq.Qualid -> Coq.Term
genericForFree typeTerm prop fv = genericApply Coq.Base.forFree [] []
  [typeTerm, Coq.Qualid prop, Coq.Qualid fv]

-------------------------------------------------------------------------------
-- Free Monad Operations                                                     --
-------------------------------------------------------------------------------
-- | Wraps the given Coq term with the @pure@ constructor of the @Free@ monad.
generatePure :: Coq.Term -> Converter Coq.Term
generatePure = return . Coq.app (Coq.Qualid Coq.Base.freePureCon) . (: [])

-- | Generates a Coq expression that binds the given values to fresh variables
--   if the position in the given @[Bool]@ list is @True@.
--
--   The fresh variables and the not bound values are passed to the given
--   function in their original order. The fresh variables are not visible
--   outside this function. If a value is a variable, the name of that variable
--   is used as the prefix of the corresponding fresh variable. Otherwise, the
--   given default prefix is used.
--
--   If some given type is @Nothing@, the type of the fresh variable is
--   inferred by Coq.
generateBinds
  :: [Coq.Term]       -- ^ The values to bind or pass through.
  -> String           -- ^ A prefix to use for fresh variables by default.
  -> [Bool]           -- ^ If each value should be bound or passed through.
  -> [Maybe Coq.Term] -- ^ The types of the values to bind.
  -> ([Coq.Term] -> Converter Coq.Term)
  -- ^ Converter for the right-hand side of the generated
  --   function. The first argument are the fresh variables
  --   and passed through values.
  -> Converter Coq.Term
generateBinds exprs' defaultPrefix areStrict argTypes' generateRHS
  = generateBinds' (zip3 exprs' (areStrict ++ repeat False)
                    (argTypes' ++ repeat Nothing)) []
 where
  generateBinds'
    :: [(Coq.Term, Bool, Maybe Coq.Term)] -> [Coq.Term] -> Converter Coq.Term
  generateBinds' [] acc = generateRHS acc
  generateBinds' ((expr', isStrict, argType') : xs) acc
    = if isStrict then generateBind expr' defaultPrefix argType' $ \arg ->
      generateBinds' xs (acc ++ [arg]) else generateBinds' xs (acc ++ [expr'])

-- | Generates a Coq expressions that binds the given value to a fresh variable.
--
--   The generated fresh variable is passed to the given function. It is not
--   visible outside of that function. If the given expression is a variable,
--   the name of that variable is used as the prefix of the fresh variable.
--   Otherwise the given default prefix is used.
--
--   If the given expression is an application of the @pure@ constructor,
--   no bind will be generated. The wrapped value is passed directly to
--   the given function instead of a fresh variable.
--
--   If the third argument is @Nothing@, the type of the fresh variable is
--   inferred by Coq.
generateBind
  :: Coq.Term
  -- ^ The left-hand side of the bind operator.
  -> String
  -- ^ A prefix to use for fresh variable by default.
  -> Maybe Coq.Term
  -- ^ The Coq type of the value to bind or @Nothing@ if it should be inferred
  --   by Coq.
  -> (Coq.Term -> Converter Coq.Term)
  -- ^ Converter for the right-hand side of the generated
  --   function. The first argument is the fresh variable.
  -> Converter Coq.Term
generateBind (Coq.App (Coq.Qualid con) (Coq.PosArg arg :| [])) _ _ generateRHS
  | con == Coq.Base.freePureCon = generateRHS arg
generateBind expr' defaultPrefix argType' generateRHS = localEnv $ do
  x <- freshCoqQualid (suggestPrefixFor expr')
  rhs <- generateRHS (Coq.Qualid x)
  return
    (Coq.app (Coq.Qualid Coq.Base.freeBind) [expr', Coq.fun [x] [argType'] rhs])
 where
  -- | Suggests a prefix for the fresh variable the given expression
  --   is bound to.
  suggestPrefixFor :: Coq.Term -> String
  suggestPrefixFor (Coq.Qualid qualid) = maybe defaultPrefix removeIndex
    (Coq.unpackQualid qualid)
  suggestPrefixFor _                   = defaultPrefix

  -- | Removes a trailing underscore and number from the given string.
  removeIndex :: String -> String
  removeIndex ident = case elemIndex '_' ident of
    Just usIndex -> take usIndex ident
    Nothing      -> ident
