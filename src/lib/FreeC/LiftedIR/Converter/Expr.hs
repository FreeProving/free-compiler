-- | Implements the IR to lifted IR translation for expressions.

module FreeC.LiftedIR.Converter.Expr
  ( convertExpr
  )
where

import           Control.Monad                  ( foldM
                                                , join
                                                )
import           Data.Foldable                  ( foldrM )
import           Data.Maybe                     ( fromMaybe )

import qualified FreeC.IR.Syntax               as IR
import           FreeC.IR.SrcSpan               ( SrcSpan(NoSrcSpan) )
import qualified FreeC.LiftedIR.Syntax         as LIR
import qualified FreeC.LiftedIR.Converter.Type as LIR
import           FreeC.Environment
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter           ( reportFatal
                                                , Message(Message)
                                                , Severity(Internal)
                                                )

-- | Converts an expression from IR to lifted IR and lifts it during the
--   translation.
--
convertExpr :: IR.Expr -> Converter LIR.Expr
convertExpr expr = convertExpr' expr [] []

-- | Same as @convertExpr@ but accumulates arguments.
--
--   This function always produces a term of type @Free S P τ*@.
--   The accumulation of arguments is needed to reason about fully applied
--   functions. Top level functions and constructors are lifted argument wise.
--   Translating them with out considering all arguments would violate the
--   invariant.
--
--   > e : τ ↦ e' : τ'
convertExpr' :: IR.Expr -> [IR.Type] -> [IR.Expr] -> Converter LIR.Expr

-- Pass argument from applications to converter for callee, allowing us to
-- convert functions and constructors with full access to their parameters.
--
-- >                $
-- > convertExpr'  / \   [] args = convertExpr' e₁ [] (e₂ : args)
-- >              e₁  e₂
convertExpr' (IR.App _ e1 e2 _) [] args = convertExpr' e1 [] (e2 : args)

-- Pass type argument from visible type application to converter for callee.
--
-- >                @
-- > convertExpr'  / \   tArgs args = convertExpr' e (τ : tArgs) args
-- >              e   τ
convertExpr' (IR.TypeAppExpr _ e t _) typeArgs args =
  convertExpr' e (t : typeArgs) args

-- Constructors.
convertExpr' (IR.Con srcSpan name _) _ args = do
  args' <- mapM convertExpr args
  let con = LIR.SmartCon srcSpan name
  return $ LIR.App srcSpan con [] [] args'

-- Cases for (possible applied) variables (i.e. variables and functions).
convertExpr' (IR.Var srcSpan name _) _ args = do
  args' <- mapM convertExpr args
  let varName = LIR.Var srcSpan name
  function <- inEnv $ isFunction name
  if function -- If this is a top level functions it's lifted argument wise.
    then return $ LIR.App srcSpan varName [] [] args'
    else generateApply varName args'

-- Integer Literals.
convertExpr' (IR.IntLiteral srcSpan value _) [] [] =
  return $ LIR.Pure srcSpan $ LIR.IntLiteral srcSpan value

-- Lambda abstractions.
--
-- > ⎡     Γ,x:τ₀ ⊢ e:τ₁     ⎤'           Γ',x:τ₀' ⊢ e':τ₁'
-- > ⎢-----------------------⎥ = -----------------------------------
-- > ⎣ Γ ⊢ λx:τ₀.e : τ₀ → τ₁ ⎦   Γ' ⊢ pure(λx:τ₀'.e') : m(τ₀' → τ₁')
convertExpr' (IR.Lambda srcSpan args rhs _) [] [] =
  flip (foldr (\a b -> LIR.Pure srcSpan $ LIR.Lambda srcSpan [a] b))
       (map convertVarPat args)
    <$> convertExpr rhs

  -- LIR.Pure srcSpan
  --   <$> (LIR.Lambda srcSpan (map convertVarPat args) <$> convertExpr rhs)

-- @if@-expressions.
--
-- > ⎡Γ ⊢ p:Bool  Γ ⊢ t:τ  Γ ⊢ f:τ⎤'     Γ' ⊢ p':Bool'  Γ' ⊢ t':τ'  Γ' ⊢ f':τ'
-- > ⎢----------------------------⎥ = -------------------------------------------
-- > ⎣ Γ ⊢ if p then t else f : τ ⎦   Γ' ⊢ p' >>= λx:𝔹'.if x then t' else f' : τ'
--
-- Note that the argument of the lambda is lifted, but its type is
-- @Bool Shape Pos@, which is just an alias for @bool@, which ignores its
-- arguments.
convertExpr' (IR.If srcSpan cond true false _) [] [] = do
  cond' <- convertExpr cond
  cond' `bind` \d -> LIR.If srcSpan d <$> convertExpr true <*> convertExpr false

-- @case@-expressions.
--
-- > ⎡Γ ⊢ e:τ₀   Γ ⊢ alts:τ₀ => τ⎤'     Γ' ⊢ e':τ₀'     Γ' ⊢ alts':τ₀* => τ'
-- > ⎢---------------------------⎥ = ------------------------------------------
-- > ⎣  Γ ⊢ case e of alts : τ   ⎦   Γ' ⊢ e' >>= λx:τ₀*.match x with alts' : τ'
--
-- where @alts'@ are the lifted (not smart) constructors for τ₀.
convertExpr' (IR.Case srcSpan discriminante patterns _) [] [] = do
  discriminant' <- convertExpr discriminante
  discriminant' `bind` \d -> LIR.Case srcSpan d <$> mapM convertAlt patterns

convertExpr' (IR.Undefined srcSpan _) _ _ = return $ LIR.Undefined srcSpan

convertExpr' (IR.ErrorExpr srcSpan msg _) _ _ =
  return $ LIR.ErrorExpr srcSpan msg

-- Visible type application of an expression other than a function or
-- constructor.
convertExpr' expr (_ : _) _ =
  reportFatal
    $  Message (IR.exprSrcSpan expr) Internal
    $  "Only type arguments of functions and constructors can be "
    ++ "applied visibly."

-- Application of an expression other than a function or constructor
-- application. We use an as-pattern for @args@ such that we get a compile
-- time warning when a node is added to the AST that we do not cover above.
convertExpr' expr [] args@(_ : _) =
  join $ generateApply <$> convertExpr expr <*> mapM convertExpr args

-------------------------------------------------------------------------------
-- Lift Patterns                                                             --
-------------------------------------------------------------------------------

-- | Translates a case alternative pattern from IR to LIR, by lifting the pattern
--   and the right-hand side.
convertAlt :: IR.Alt -> Converter LIR.Alt
convertAlt (IR.Alt srcSpan conPat varPats expr) =
  LIR.Alt srcSpan (convertConPat conPat) (map convertVarPat varPats)
    <$> convertExpr expr

-- | Translates a constructor pattern from IR to LIR.
convertConPat :: IR.ConPat -> LIR.ConPat
convertConPat (IR.ConPat srcSpan name) = LIR.ConPat srcSpan name

-- | Translates a variable pattern from IR to LIR.
--
--   The bound variable is not added to the environment, because the same IR name
--   could refer to different variables (e.g. shadowing, two @case@ branches
--   biding the same name). In the back end this can be solved using @localEnv@.
convertVarPat :: IR.VarPat -> LIR.VarPat
convertVarPat (IR.VarPat srcSpan name t _) = do
  LIR.VarPat srcSpan (IR.UnQual $ IR.Ident name) $ LIR.liftType <$> t

-------------------------------------------------------------------------------
-- Application-expression helper                                             --
-------------------------------------------------------------------------------

-- | Applies a n-ary lifted function by applying the rule below repeatedly.
--
--   > ⎡Γ ⊢ e₀:τ₀ → τ₁   Γ ⊢ e₁:τ₀⎤'  Γ' ⊢ e₀' : m(τ₀' → τ₁')    Γ' ⊢ e₁':τ₀'
--   > ⎢--------------------------⎥ = ---------------------------------------
--   > ⎣      Γ ⊢ e₀e₁ : τ₁       ⎦   Γ' ⊢ e₀' >>= λf:(τ₀' → τ₁').f e₀' : e₁'
generateApply :: LIR.Expr -> [LIR.Expr] -> Converter LIR.Expr
generateApply = foldM $ \mf arg -> mf `bind` \f -> return (f `app` arg)
  where app l r = LIR.App NoSrcSpan l [] [] [r]

-------------------------------------------------------------------------------
-- Bind Expression                                                           --
-------------------------------------------------------------------------------

-- | Tries to extract a variable name from an expression. This function can be
--   used to preserve the same base variable name across chains of binds.
guessName :: LIR.Expr -> Maybe String
guessName (LIR.Var _ name  ) = IR.identFromQName name
guessName (LIR.Bind _ arg _) = guessName arg
guessName _                  = Nothing

-- | Creates a @>>= \x ->@, which binds a new variable.
--
--   The bound variable is not added to the environment, because the same IR name
--   could refer to different variables (e.g. shadowing, two @case@ branches
--   binding the same name). In the back end this can be solved using @localEnv@.
bind :: LIR.Expr -> (LIR.Expr -> Converter LIR.Expr) -> Converter LIR.Expr
bind arg k = do
  let argIdent = IR.UnQual $ IR.Ident $ "uf"  -- fromMaybe "f" (guessName arg)
  let varPat   = LIR.VarPat NoSrcSpan argIdent Nothing
  rhs <- LIR.Lambda NoSrcSpan [varPat] <$> k (LIR.Var NoSrcSpan argIdent)
  return $ LIR.Bind NoSrcSpan arg rhs






