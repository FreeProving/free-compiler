-- | This module contains functions for converting Haskell expressions to Coq.

module FreeC.Backend.Coq.Converter.Expr where

import           Control.Monad.Extra            ( ifM
                                                , when
                                                )
import           Data.Composition
import           Data.Foldable                  ( foldlM
                                                , foldrM
                                                )

import qualified FreeC.Backend.Coq.Base        as Coq.Base
import           FreeC.Backend.Coq.Converter.Arg
import           FreeC.Backend.Coq.Converter.Free
import           FreeC.Backend.Coq.Converter.Type
import qualified FreeC.Backend.Coq.Syntax      as Coq
import           FreeC.Environment
import           FreeC.Environment.Fresh
import           FreeC.Environment.LookupOrFail
import           FreeC.Environment.Renamer
import qualified FreeC.IR.Base.Prelude         as IR.Prelude
import           FreeC.IR.SrcSpan
import           FreeC.IR.Subst
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pretty

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Converts a Haskell expression to Coq.
convertExpr :: IR.Expr -> Converter Coq.Term
convertExpr expr = convertExpr' expr [] []

-- | Converts the application of a Haskell expression to the given arguments
--   and visibly applied type arguments to Coq.
convertExpr' :: IR.Expr -> [IR.Type] -> [IR.Expr] -> Converter Coq.Term

-- Constructors.
--
-- Partially applied constructors are not evaluated in Haskell and therefor
-- cannot be @⊥@. The translated type of a constructor @C : τ₀ -> … -> τₙ@ is
-- @c : τ₀' -> … -> τₙ*@ instead of @m(τ₀' -> m(τ₁' -> m(… -> τₙ')))@.
--
-- Note that the return type is translated using * not ', because a constructor
-- in Coq cannot return a wrapped value. A smart constructor @C@ is generated,
-- which wrapps the value of @c@. It is therefore sufficient to just convert
-- and apply the arguments.
convertExpr' (IR.Con srcSpan name _) typeArgs args = do
  qualid            <- lookupSmartIdentOrFail srcSpan name
  typeArgs'         <- mapM convertType' typeArgs
  args'             <- mapM convertExpr args
  Just arity        <- inEnv $ lookupArity IR.ValueScope name
  Just typeArgArity <- inEnv $ lookupTypeArgArity IR.ValueScope name
  let typeArgCount = length typeArgs'
  when (typeArgCount /= typeArgArity)
    $  reportFatal
    $  Message srcSpan Internal
    $  "The constructor '"
    ++ showPretty name
    ++ "' is applied to the wrong number of type arguments.\n"
    ++ "Expected "
    ++ show typeArgArity
    ++ " type arguments, got "
    ++ show typeArgCount
    ++ "."
  generateApplyN arity (genericApply qualid [] typeArgs' []) args'

-- Functions and variables.
convertExpr' (IR.Var srcSpan name _) typeArgs args = do
  qualid    <- lookupIdentOrFail srcSpan IR.ValueScope name
  typeArgs' <- mapM convertType' typeArgs
  args'     <- mapM convertExpr args
  -- The number of type arguments must match the number of type parameters.
  -- In case of variables, there must be no type arguments.
  -- Since, the user cannot create visible type applications, it is an
  -- internal error if the number of type arguments does not match.
  let typeArgCount = length typeArgs
  maybeTypeArgArity <- inEnv $ lookupTypeArgArity IR.ValueScope name
  case maybeTypeArgArity of
    Just typeArgArity ->
      when (typeArgCount /= typeArgArity)
        $  reportFatal
        $  Message srcSpan Internal
        $  "The function '"
        ++ showPretty name
        ++ "' is applied to the wrong number of type arguments.\n"
        ++ "Expected "
        ++ show typeArgArity
        ++ " type arguments, got "
        ++ show typeArgCount
        ++ "."
    Nothing ->
      when (typeArgCount /= 0)
        $  reportFatal
        $  Message srcSpan Internal
        $  "The variable '"
        ++ showPretty name
        ++ "' must not be applied to type arguments.\n"
        ++ "Got "
        ++ show typeArgCount
        ++ " type arguments."
  -- Is this a variable or function?
  function <- inEnv $ isFunction name
  if function
    then do
      -- Add the arguments of the @Free@ monad if necessary. If the function
      -- is partial, we need to add the @Partial@ instance as well.
      partialArg <- ifM (inEnv $ isPartial name)
                        (return [Coq.Qualid (fst Coq.Base.partialArg)])
                        (return [])
      callee <- ifM (inEnv $ needsFreeArgs name)
                    (return (genericApply qualid partialArg typeArgs' []))
                    (return (Coq.app (Coq.Qualid qualid) partialArg))
      -- Is this a recursive helper function?
      Just arity   <- inEnv $ lookupArity IR.ValueScope name
      mDecArgIndex <- inEnv $ lookupFirstStrictArgIndex name
      case mDecArgIndex of
        Nothing ->
          -- Regular functions can be applied directly.
          generateApplyN arity callee args'
        Just index -> do
          -- The decreasing argument of a recursive helper function must be
          -- unwrapped first.
          let (before, decArg : after) = splitAt index args'
          -- Add type annotation for decreasing argument.
          Just typeArgIdents <- inEnv $ lookupTypeArgs IR.ValueScope name
          Just argTypes      <- inEnv $ lookupArgTypes IR.ValueScope name
          let typeArgNames = map (IR.UnQual . IR.Ident) typeArgIdents
              subst = composeSubsts (zipWith singleSubst typeArgNames typeArgs)
              decArgType = applySubst subst (argTypes !! index)
          decArgType' <- mapM convertType' decArgType
          generateBind decArg freshArgPrefix decArgType' $ \decArg' ->
            generateApplyN arity callee (before ++ decArg' : after)
    else do
      -- If this is the decreasing argument of a recursive helper function,
      -- it must be lifted into the @Free@ monad.
      pureArg <- inEnv $ isPureVar name
      if pureArg
        then generatePure (Coq.Qualid qualid) >>= flip generateApply args'
        else generateApply (Coq.Qualid qualid) args'

-- Pass argument from applications to converter for callee, allowing us to
-- convert functions and constructors with full access to their parameters.
-- >                $
-- > convertExpr'  / \   [] args = convertExpr' e₁ [] (e₂ : args)
-- >              e₁  e₂
convertExpr' (IR.App _ e1 e2 _) [] args = convertExpr' e1 [] (e2 : args)

-- Pass type argument from visible type application to converter for callee.
-- >                @
-- > convertExpr'  / \   tArgs args = convertExpr' e (τ : tArgs) args
-- >              e   τ
convertExpr' (IR.TypeAppExpr _ e t _) typeArgs args =
  convertExpr' e (t : typeArgs) args

-- @if@-expressions.
--
-- > ⎡Γ ⊢ p:Bool  Γ ⊢ t:τ  Γ ⊢ f:τ⎤'     Γ' ⊢ p':Bool'  Γ' ⊢ t':τ'  Γ' ⊢ f':τ'
-- > ⎢――――――――――――――――――――――――――――⎥ = ―――――――――――――――――――――――――――――――――――――――――――
-- > ⎣ Γ ⊢ if p then t else f : τ ⎦   Γ' ⊢ p' >>= λx:𝔹'.if x then t' else f' : τ'
--
-- Note that the argument of the lambda is lifted, but its type is @Bool Shape Pos@,
-- which is just an alias for @bool@, which ignores its arguments.
convertExpr' (IR.If _ e1 e2 e3 _) [] [] = do
  e1'   <- convertExpr e1
  bool' <- convertType' (IR.TypeCon NoSrcSpan IR.Prelude.boolTypeConName)
  generateBind e1' freshBoolPrefix (Just bool') $ \cond -> do
    e2' <- convertExpr e2
    e3' <- convertExpr e3
    return (Coq.If Coq.SymmetricIf cond Nothing e2' e3')

-- @case@-expressions.
--
-- > ⎡Γ ⊢ e:τ₀   Γ ⊢ alts:τ₀ => τ⎤'     Γ' ⊢ e':τ₀'     Γ' ⊢ alts':τ₀* => τ'
-- > ⎢―――――――――――――――――――――――――――⎥ = ――――――――――――――――――――――――――――――――――――――――――
-- > ⎣  Γ ⊢ case e of alts : τ   ⎦   Γ' ⊢ e' >>= λx:τ₀*.match x with alts' : τ'
--
-- where @alts'@ are the lifted (not smart) constructors for τ₀.
convertExpr' (IR.Case _ expr alts _) [] [] = do
  expr' <- convertExpr expr
  generateBind expr' freshArgPrefix Nothing $ \value -> do
    alts' <- mapM convertAlt alts
    return (Coq.match value alts')

-- Error terms.
convertExpr' (IR.Undefined srcSpan _) typeArgs [] = do
  when (length typeArgs /= 1)
    $  reportFatal
    $  Message srcSpan Internal
    $  "The error term 'undefined' is applied to the wrong number of "
    ++ "type arguments.\n"
    ++ "Expected 1 type arguments, got "
    ++ show (length typeArgs)
    ++ "."
  let partialArg = Coq.Qualid (fst Coq.Base.partialArg)
  typeArgs' <- mapM convertType' typeArgs
  return (genericApply Coq.Base.partialUndefined [partialArg] typeArgs' [])

convertExpr' (IR.ErrorExpr srcSpan msg _) typeArgs [] = do
  when (length typeArgs /= 1)
    $  reportFatal
    $  Message srcSpan Internal
    $  "The error term 'error "
    ++ show msg
    ++ "' is applied to the wrong number of type arguments.\n"
    ++ "Expected 1 type arguments, got "
    ++ show (length typeArgs)
    ++ "."
  let partialArg = Coq.Qualid (fst Coq.Base.partialArg)
  typeArgs' <- mapM convertType' typeArgs
  return
    (genericApply Coq.Base.partialError
                  [partialArg]
                  typeArgs'
                  [Coq.InScope (Coq.string msg) Coq.Base.stringScope]
    )

-- Integer literals.
convertExpr' (IR.IntLiteral _ value _) [] [] = do
  let natValue = Coq.Num (fromInteger (abs value))
      value' | value < 0 = Coq.app (Coq.Qualid (Coq.bare "-")) [natValue]
             | otherwise = natValue
  generatePure (Coq.InScope value' Coq.Base.integerScope)

-- Lambda abstractions.
--
-- > ⎡     Γ,x:τ₀ ⊢ e:τ₁      ⎤'            Γ',x:τ₀' ⊢ e':τ₁'
-- > ⎢――――――――――――――――――――――――⎥ = ――――――――――――――――――――――――――――――――――――――
-- > ⎣ Γ ⊢ λx:τ₀.e : τ₀ -> τ₁ ⎦    Γ' ⊢ pure(λx:τ₀'.e') : m(τ₀' -> τ₁')
--
convertExpr' (IR.Lambda _ args expr _) [] [] = localEnv $ do
  args' <- mapM convertArg args
  expr' <- convertExpr expr
  foldrM (generatePure .: Coq.Fun . return) expr' args'

-- Visible type application of an expression other than a function or
-- constructor.
convertExpr' expr (_ : _) _ =
  reportFatal
    $  Message (IR.exprSrcSpan expr) Internal
    $  "Only type arguments of functions and constructors can be "
    ++ "applied visibly."

-- Application of an expression other than a function or constructor
-- application. We use an as-pattern for @args@ such that we get a compile
-- time warning when a node is added to the AST that we do not conver above.
convertExpr' expr [] args@(_ : _) = do
  expr' <- convertExpr' expr [] []
  args' <- mapM convertExpr args
  generateApply expr' args'

-------------------------------------------------------------------------------
-- Application-expression helpers                                            --
-------------------------------------------------------------------------------

-- | Generates a Coq term for applying a monadic term to the given arguments.
generateApply :: Coq.Term -> [Coq.Term] -> Converter Coq.Term
generateApply = foldlM $ \term arg ->
  generateBind term freshFuncPrefix Nothing (\f -> return (Coq.app f [arg]))

-- | Generates a Coq term for applying a function with the given arity to
--   the given arguments.
--
--   If there are too many arguments, the remaining arguments are applied
--   using 'generateApply'. There should not be too few arguments (i.e. the
--   function should be fully applied).
generateApplyN :: Int -> Coq.Term -> [Coq.Term] -> Converter Coq.Term
generateApplyN arity term args =
  generateApply (Coq.app term (take arity args)) (drop arity args)

-------------------------------------------------------------------------------
-- Case-expression helpers                                                   --
-------------------------------------------------------------------------------

-- | Converts an alternative of a Haskell @case@-expressions to Coq.
convertAlt :: IR.Alt -> Converter Coq.Equation
convertAlt (IR.Alt _ conPat varPats expr _) = localEnv $ do
  conPat' <- convertConPat conPat varPats
  expr'   <- convertExpr expr
  return (Coq.equation conPat' expr')

-- | Converts a Haskell constructor pattern with the given variable pattern
--   arguments to a Coq pattern.
convertConPat :: IR.ConPat -> [IR.VarPat] -> Converter Coq.Pattern
convertConPat (IR.ConPat srcSpan ident) varPats = do
  qualid   <- lookupIdentOrFail srcSpan IR.ValueScope ident
  varPats' <- mapM convertVarPat varPats
  return (Coq.ArgsPat qualid varPats')

-- | Converts a Haskell variable pattern to a Coq variable pattern.
--
--   The types of variable patterns are not annotated in Coq.
convertVarPat :: IR.VarPat -> Converter Coq.Pattern
convertVarPat (IR.VarPat srcSpan ident maybeVarType _) = do
  ident' <- renameAndDefineVar srcSpan False ident maybeVarType
  return (Coq.QualidPat ident')
