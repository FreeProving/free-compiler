-- | Implements the IR to lifted IR translation for expressions.

module FreeC.LiftedIR.Converter.Expr
  ( liftExpr
  )
where

import           Control.Monad                  ( join )
import           Data.Maybe                     ( fromMaybe )

import qualified FreeC.IR.Syntax               as IR
import           FreeC.IR.Syntax.Name           ( identFromQName )
import           FreeC.IR.SrcSpan               ( SrcSpan(NoSrcSpan) )
import qualified FreeC.LiftedIR.Syntax         as LIR
import qualified FreeC.LiftedIR.Converter.Type as LIR
import           FreeC.Environment
import           FreeC.Environment.LookupOrFail ( lookupAgdaFreshIdentOrFail
                                                , lookupAgdaValIdentOrFail
                                                )
import           FreeC.Environment.Renamer      ( renameAndDefineAgdaVar )
import           FreeC.Environment.Fresh        ( freshIRQName )
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter           ( reportFatal
                                                , Message(Message)
                                                , Severity(Internal)
                                                )

-- | Converts an expression from IR to lifted IR and lifts it during the
--   translation.
liftExpr :: IR.Expr -> Converter LIR.Expr
liftExpr expr = liftExpr' expr [] []

-- | Same as @liftExpr@ but accumulates arguments.
--
--   This function always produces a term of type @Free S P τ*@.
--   The accumulation of arguments is needed to reason about fully applied
--   functions. Top level functions and constructors are lifted argument wise.
--   Translating them with out considering all arguments would violate the
--   invariant.
--
--   > e : τ ↦ e' : τ'
liftExpr' :: IR.Expr -> [IR.Type] -> [IR.Expr] -> Converter LIR.Expr

-- Pass argument from applications to converter for callee, allowing us to
-- convert functions and constructors with full access to their parameters.
--
-- >                $
-- > liftExpr'  / \   [] args = liftExpr' e₁ [] (e₂ : args)
-- >              e₁  e₂
liftExpr' (IR.App _ e1 e2 _) [] args = liftExpr' e1 [] (e2 : args)

-- Pass type argument from visible type application to converter for callee.
--
-- >                @
-- > liftExpr'  / \   tArgs args = liftExpr' e (τ : tArgs) args
-- >              e   τ
liftExpr' (IR.TypeAppExpr _ e t _) typeArgs args =
  liftExpr' e (t : typeArgs) args

-- Constructors.
liftExpr' (IR.Con srcSpan name _) _ args = do
  args' <- mapM liftExpr args
  let con = LIR.SmartCon srcSpan name
  return $ LIR.App srcSpan con [] [] args'

-- Cases for (possible applied) variables (i.e. variables and functions).
liftExpr' (IR.Var srcSpan name _) _ args = do
  args'    <- mapM liftExpr args
  varName  <- LIR.Var srcSpan name <$> lookupAgdaValIdentOrFail srcSpan name
  function <- inEnv $ isFunction name
  if function -- If this is a top level functions it's lifted argument wise.
    then return $ LIR.App srcSpan varName [] [] args'
    else generateApply varName args'

-- Integer Literals.
liftExpr' (IR.IntLiteral srcSpan value _) [] [] =
  return $ LIR.Pure srcSpan $ LIR.IntLiteral srcSpan value

-- Lambda abstractions.
--
-- > ⎡     Γ,x:τ₀ ⊢ e:τ₁     ⎤'           Γ',x:τ₀' ⊢ e':τ₁'
-- > ⎢-----------------------⎥ = -----------------------------------
-- > ⎣ Γ ⊢ λx:τ₀.e : τ₀ → τ₁ ⎦   Γ' ⊢ pure(λx:τ₀'.e') : m(τ₀' → τ₁')
liftExpr' (IR.Lambda srcSpan args rhs _) [] [] =
  localEnv
    $   flip (foldr (\a b -> LIR.Pure srcSpan $ LIR.Lambda srcSpan [a] b))
    <$> mapM convertVarPat args
    <*> liftExpr rhs

-- @if@-expressions.
--
-- > ⎡Γ ⊢ p:Bool  Γ ⊢ t:τ  Γ ⊢ f:τ⎤'     Γ' ⊢ p':Bool'  Γ' ⊢ t':τ'  Γ' ⊢ f':τ'
-- > ⎢----------------------------⎥ = -------------------------------------------
-- > ⎣ Γ ⊢ if p then t else f : τ ⎦   Γ' ⊢ p' >>= λx:𝔹'.if x then t' else f' : τ'
--
-- Note that the argument of the lambda is lifted, but its type is
-- @Bool Shape Pos@, which is just an alias for @bool@, which ignores its
-- arguments.
liftExpr' (IR.If srcSpan cond true false _) [] [] = do
  cond' <- liftExpr cond
  cond' `bind` \d -> LIR.If srcSpan d <$> liftExpr true <*> liftExpr false

-- @case@-expressions.
--
-- > ⎡Γ ⊢ e:τ₀   Γ ⊢ alts:τ₀ => τ⎤'     Γ' ⊢ e':τ₀'     Γ' ⊢ alts':τ₀* => τ'
-- > ⎢---------------------------⎥ = ------------------------------------------
-- > ⎣  Γ ⊢ case e of alts : τ   ⎦   Γ' ⊢ e' >>= λx:τ₀*.match x with alts' : τ'
--
-- where @alts'@ are the lifted (not smart) constructors for τ₀.
liftExpr' (IR.Case srcSpan discriminante patterns _) [] [] = do
  discriminant' <- liftExpr discriminante
  discriminant' `bind` \d -> LIR.Case srcSpan d <$> mapM convertAlt patterns

liftExpr' (IR.Undefined srcSpan _    ) _ _ = return $ LIR.Undefined srcSpan

liftExpr' (IR.ErrorExpr srcSpan msg _) _ _ = return $ LIR.ErrorExpr srcSpan msg

-- Visible type application of an expression other than a function or
-- constructor.
liftExpr' expr (_ : _) _ =
  reportFatal
    $  Message (IR.exprSrcSpan expr) Internal
    $  "Only type arguments of functions and constructors can be "
    ++ "applied visibly."

-- Application of an expression other than a function or constructor
-- application. We use an as-pattern for @args@ such that we get a compile
-- time warning when a node is added to the AST that we do not cover above.
liftExpr' expr [] args@(_ : _) =
  join $ generateApply <$> liftExpr expr <*> mapM liftExpr args

-------------------------------------------------------------------------------
-- Lift Patterns                                                             --
-------------------------------------------------------------------------------

-- | Translates a case alternative pattern from IR to LIR, by lifting the pattern
--   and the right-hand side.
convertAlt :: IR.Alt -> Converter LIR.Alt
convertAlt (IR.Alt srcSpan conPat varPats expr) =
  LIR.Alt srcSpan (convertConPat conPat)
    <$> mapM convertVarPat varPats
    <*> liftExpr expr

-- | Translates a constructor pattern from IR to LIR.
convertConPat :: IR.ConPat -> LIR.ConPat
convertConPat (IR.ConPat srcSpan name) = LIR.ConPat srcSpan name

-- | Translates a variable pattern from IR to LIR.
convertVarPat :: IR.VarPat -> Converter LIR.VarPat
convertVarPat (IR.VarPat srcSpan name t strict) =
  LIR.VarPat srcSpan name (LIR.liftType <$> t)
    <$> renameAndDefineAgdaVar srcSpan strict name t

-------------------------------------------------------------------------------
-- Application-expression helper                                             --
-------------------------------------------------------------------------------

-- | Applies a n-ary lifted function by applying the rule below repeatedly.
--
--   > ⎡Γ ⊢ e₀:τ₀ → τ₁   Γ ⊢ e₁:τ₀⎤'  Γ' ⊢ e₀' : m(τ₀' → τ₁')    Γ' ⊢ e₁':τ₀'
--   > ⎢--------------------------⎥ = ---------------------------------------
--   > ⎣      Γ ⊢ e₀e₁ : τ₁       ⎦   Γ' ⊢ e₀' >>= λf:(τ₀' → τ₁').f e₀' : e₁'
generateApply :: LIR.Expr -> [LIR.Expr] -> Converter LIR.Expr
generateApply mf []       = return mf
generateApply mf (a : as) = mf `bind` \f -> generateApply (f `app` a) as
  where app l r = LIR.App NoSrcSpan l [] [] [r]

-------------------------------------------------------------------------------
-- Bind Expression                                                           --
-------------------------------------------------------------------------------

-- | Tries to extract a variable name from an expression. This function can be
--   used to preserve the same base variable name across chains of binds.
guessName :: LIR.Expr -> Maybe String
guessName (LIR.Var  _ name _) = IR.identFromQName name
guessName (LIR.Bind _ arg  _) = guessName arg
guessName _                   = Nothing

-- | Creates a @>>= \x ->@, which binds a new variable.
bind :: LIR.Expr -> (LIR.Expr -> Converter LIR.Expr) -> Converter LIR.Expr
bind arg k = localEnv $ do
  -- Generate a new name for lambda argument.
  argIdent <- freshIRQName $ fromMaybe "f" (guessName arg)
  let Just argIdent' = identFromQName argIdent
  -- Build the lambda on the RHS of the bind.
  argAgda <- lookupAgdaFreshIdentOrFail NoSrcSpan argIdent
  let varPat = LIR.VarPat NoSrcSpan argIdent' Nothing $ argAgda
  rhs <- LIR.Lambda NoSrcSpan [varPat]
    <$> k (LIR.Var NoSrcSpan argIdent argAgda)
  -- Build the bind.
  return $ LIR.Bind NoSrcSpan arg rhs
