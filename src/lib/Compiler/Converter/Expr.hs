-- | This module contains functions for converting Haskell expressions to Coq.

module Compiler.Converter.Expr where

import           Data.Composition
import           Data.Foldable                  ( foldrM )
import           Data.Maybe                     ( maybe )

import           Compiler.Converter.Arg
import           Compiler.Converter.Type
import           Compiler.Converter.Free
import qualified Compiler.Coq.AST              as G
import qualified Compiler.Coq.Base             as CoqBase
import           Compiler.Environment
import           Compiler.Environment.Fresh
import           Compiler.Environment.LookupOrFail
import           Compiler.Environment.Renamer
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.SrcSpan
import           Compiler.Monad.Converter
import           Compiler.Monad.Instance.Fail   ( )

-------------------------------------------------------------------------------
-- Eta-Conversion                                                            --
-------------------------------------------------------------------------------

-- | Applies eta-abstractions to a function or constructor application util the
--   function or constructor is fully applied.
--
--   E.g. an application @f x@ of a binary function @f@ will be converted
--   to @\y -> f x y@ where @y@ is a fresh variable. This function does not
--   apply the eta-conversion recursively.
--
--   No eta-conversions are applied to nested expressions.
etaConvert :: HS.Expr -> Converter HS.Expr
etaConvert rootExpr = arityOf rootExpr >>= etaAbstractN rootExpr
 where
  -- | Determines the number of arguments expected to be passed to the given
  --   expression.
  arityOf :: HS.Expr -> Converter Int
  arityOf (HS.Con _ name) = do
    arity <- inEnv $ lookupArity ValueScope name
    return (maybe 0 id arity)
  arityOf (HS.Var _ name) = do
    arity <- inEnv $ lookupArity ValueScope name
    return (maybe 0 id arity)
  arityOf (HS.App _ e1 _) = do
    arity <- arityOf e1
    return (max 0 (arity - 1))
  arityOf _ = return 0

  -- | Applies the given number of eta-abstractions to an expression.
  etaAbstractN :: HS.Expr -> Int -> Converter HS.Expr
  etaAbstractN expr 0 = return expr
  etaAbstractN expr n = do
    x     <- freshHaskellIdent freshArgPrefix
    expr' <- etaAbstractN
      (HS.app NoSrcSpan expr [HS.Var NoSrcSpan (HS.UnQual (HS.Ident x))])
      (n - 1)
    return (HS.Lambda NoSrcSpan [HS.VarPat NoSrcSpan x] expr')

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Converts a Haskell expression to Coq.
convertExpr :: HS.Expr -> Converter G.Term
convertExpr expr = etaConvert expr >>= flip convertExpr' []

-- | Converts the application of a Haskell expression to the given arguments
--   to Coq.
--
--   This function assumes the outer most expression to be fully applied
--   by the given arguments (see also 'etaConvert').
convertExpr' :: HS.Expr -> [HS.Expr] -> Converter G.Term

-- Constructors.
convertExpr' (HS.Con srcSpan name) args = do
  qualid     <- lookupSmartIdentOrFail srcSpan name
  args'      <- mapM convertExpr args
  Just arity <- inEnv $ lookupArity ValueScope name
  generateApplyN arity (genericApply qualid []) args'

-- Functions and variables.
convertExpr' (HS.Var srcSpan name) args = do
  qualid   <- lookupIdentOrFail srcSpan ValueScope name
  args'    <- mapM convertExpr args
  -- Is this a variable or function?
  function <- inEnv $ isFunction name
  if function
    then do
    -- If the function is partial, we need to add the @Partial@ instance.
      partial <- inEnv $ isPartial name
      let partialArg = [ G.Qualid (fst CoqBase.partialArg) | partial ]
          callee     = genericApply qualid partialArg
      -- Is this a recursive helper function?
      Just arity <- inEnv $ lookupArity ValueScope name
      mDecArg    <- inEnv $ lookupDecArg name
      case mDecArg of
        Nothing ->
          -- Regular functions can be applied directly.
          generateApplyN arity callee args'
        Just index -> do
          -- The decreasing argument of a recursive helper function must be
          -- unwrapped first.
          let (before, decArg : after) = splitAt index args'
          -- Add type annotation for decreasing argument.
          Just argTypes <- inEnv $ lookupArgTypes ValueScope name
          decArgType'   <- mapM convertType' (argTypes !! index)
          generateBind decArg decArgType' $ \decArg' ->
            generateApplyN arity callee (before ++ decArg' : after)
    else do
      -- If this is the decreasing argument of a recursive helper function,
      -- it must be lifted into the @Free@ monad.
      pureArg <- inEnv $ isPureVar name
      if pureArg
        then generatePure (G.Qualid qualid) >>= flip generateApply args'
        else generateApply (G.Qualid qualid) args'

-- Pass argument from applications to converter for callee.
convertExpr' (HS.App _ e1 e2  ) args = convertExpr' e1 (e2 : args)

-- @if@-expressions.
convertExpr' (HS.If _ e1 e2 e3) []   = do
  e1'   <- convertExpr e1
  bool' <- convertType' (HS.TypeCon NoSrcSpan HS.boolTypeConName)
  generateBind e1' (Just bool') $ \cond -> do
    e2' <- convertExpr e2
    e3' <- convertExpr e3
    return (G.If G.SymmetricIf cond Nothing e2' e3')

-- @case@-expressions.
convertExpr' (HS.Case _ expr alts) [] = do
  expr' <- convertExpr expr
  generateBind expr' Nothing $ \value -> do
    alts' <- mapM convertAlt alts
    return (G.match value alts')

-- Error terms.
convertExpr' (HS.Undefined _) [] = return (G.Qualid CoqBase.partialUndefined)
convertExpr' (HS.ErrorExpr _ msg) [] =
  return (G.app (G.Qualid CoqBase.partialError) [G.string msg])

-- Integer literals.
convertExpr' (HS.IntLiteral _ value) [] =
  generatePure (G.InScope (G.Num (fromInteger value)) (G.ident "Z"))

-- Lambda abstractions.
convertExpr' (HS.Lambda _ args expr) [] = localEnv $ do
  args' <- mapM convertInferredArg args
  expr' <- convertExpr expr
  foldrM (generatePure .: G.Fun . return) expr' args'

-- Application of an expression other than a function or constructor
-- application. (We use an as-pattern for @args@ such that we get a compile
-- time warning when a node is added to the AST that we do not conver above).
convertExpr' expr args@(_ : _) = do
  expr' <- convertExpr' expr []
  args' <- mapM convertExpr args
  generateApply expr' args'

-------------------------------------------------------------------------------
-- Application-expression helpers                                            --
-------------------------------------------------------------------------------

-- | Generates a Coq term for applying a monadic term to the given arguments.
generateApply :: G.Term -> [G.Term] -> Converter G.Term
generateApply term []           = return term
generateApply term (arg : args) = do
  term' <- generateBind term Nothing $ \f -> return (G.app f [arg])
  generateApply term' args

-- | Generates a Coq term for applying a function with the given arity to
--   the given arguments.
--
--   If there are too many arguments, the remaining arguments are applied
--   using 'generateApply'. There should not be too few arguments (i.e. the
--   function should be fully applied).
generateApplyN :: Int -> G.Term -> [G.Term] -> Converter G.Term
generateApplyN arity term args =
  generateApply (G.app term (take arity args)) (drop arity args)

-------------------------------------------------------------------------------
-- Case-expression helpers                                                   --
-------------------------------------------------------------------------------

-- | Converts an alternative of a Haskell @case@-expressions to Coq.
convertAlt :: HS.Alt -> Converter G.Equation
convertAlt (HS.Alt _ conPat varPats expr) = localEnv $ do
  conPat' <- convertConPat conPat varPats
  expr'   <- convertExpr expr
  return (G.equation conPat' expr')

-- | Converts a Haskell constructor pattern with the given variable pattern
--   arguments to a Coq pattern.
convertConPat :: HS.ConPat -> [HS.VarPat] -> Converter G.Pattern
convertConPat (HS.ConPat srcSpan ident) varPats = do
  qualid   <- lookupIdentOrFail srcSpan ValueScope ident
  varPats' <- mapM convertVarPat varPats
  return (G.ArgsPat qualid varPats')

-- | Converts a Haskell variable pattern to a Coq variable pattern.
convertVarPat :: HS.VarPat -> Converter G.Pattern
convertVarPat (HS.VarPat srcSpan ident) = do
  ident' <- renameAndDefineVar srcSpan False ident
  return (G.QualidPat (G.bare ident'))
