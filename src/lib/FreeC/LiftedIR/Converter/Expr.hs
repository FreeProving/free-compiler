module FreeC.LiftedIR.Converter.Expr
  ( convertExpr
  )
where

import           Control.Monad                  ( foldM )
import           Data.Maybe                     ( fromJust
                                                , fromMaybe
                                                )

import qualified FreeC.IR.Syntax               as IR
import           FreeC.IR.SrcSpan               ( SrcSpan(NoSrcSpan) )
import qualified FreeC.LiftedIR.Syntax         as LIR
import qualified FreeC.LiftedIR.Converter.Type as LIR
import           FreeC.Environment
import           FreeC.Environment.Fresh        ( freshIRQName )
import           FreeC.Monad.Converter

import           Prelude                 hiding ( pure )

convertExpr :: IR.Expr -> Converter LIR.Expr
convertExpr expr = convertExpr' expr [] []

-- | Converts an expression from IR to lifted IR and lifts it during the
--   translation.
--
--   TODO: state translation invariant
convertExpr' :: IR.Expr -> [IR.Type] -> [IR.Expr] -> Converter LIR.Expr

-- | Pass argument from applications to converter for callee, allowing us to
--   convert functions and constructors with full access to their parameters.
--
--   >                $
--   > convertExpr'  / \   [] args = convertExpr' e₁ [] (e₂ : args)
--   >              e₁  e₂
convertExpr' (IR.App _ e1 e2 _) [] args = convertExpr' e1 [] (e2 : args)

-- | Pass type argument from visible type application to converter for callee.
--
--   >                @
--   > convertExpr'  / \   tArgs args = convertExpr' e (τ : tArgs) args
--   >              e   τ
convertExpr' (IR.TypeAppExpr _ e t _) typeArgs args =
  convertExpr' e (t : typeArgs) args

convertExpr' (IR.Con srcSpan name _) _ args = do
  args' <- mapM convertExpr args
  let con = LIR.SmartCon srcSpan name undefined
  return $ LIR.App srcSpan con [] [] args' undefined

convertExpr' (IR.Var srcSpan name _) _ args = do
  args'    <- mapM convertExpr args
  function <- inEnv $ isFunction name
  let varName = LIR.Var srcSpan name undefined
  if function
    then -- top level function (lifted piece wise)
         return $ LIR.App srcSpan varName [] [] args' undefined
    else generateApply varName args'

-- | Integer Literals
convertExpr' (IR.IntLiteral srcSpan value _) [] [] =
  return $ pure srcSpan $ LIR.IntLiteral srcSpan value undefined

-- | Lambda abstractions.
--
-- > ⎡     Γ,x:τ₀ ⊢ e:τ₁     ⎤'           Γ',x:τ₀' ⊢ e':τ₁'
-- > ⎢-----------------------⎥ = -----------------------------------
-- > ⎣ Γ ⊢ λx:τ₀.e : τ₀ → τ₁ ⎦   Γ' ⊢ pure(λx:τ₀'.e') : m(τ₀' → τ₁')
convertExpr' (IR.Lambda srcSpan args rhs _) [] [] =
  pure srcSpan <$> (lambda srcSpan (map convertVarPat args) <$> convertExpr rhs)

-- | @if@-expressions.
--
--   > ⎡Γ ⊢ p:Bool  Γ ⊢ t:τ  Γ ⊢ f:τ⎤'     Γ' ⊢ p':Bool'  Γ' ⊢ t':τ'  Γ' ⊢ f':τ'
--   > ⎢----------------------------⎥ = -------------------------------------------
--   > ⎣ Γ ⊢ if p then t else f : τ ⎦   Γ' ⊢ p' >>= λx:𝔹'.if x then t' else f' : τ'
--
-- Note that the argument of the lambda is lifted, but its type is @Bool Shape Pos@,
-- which is just an alias for @bool@, which ignores its arguments.
convertExpr' (IR.If srcSpan cond true false _) [] [] = do
  cond' <- convertExpr cond
  cond' `bind` \d -> ite srcSpan d <$> convertExpr true <*> convertExpr false

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

-------------------------------------------------------------------------------
-- Lift Patterns                                                             --
-------------------------------------------------------------------------------

convertAlt :: IR.Alt -> Converter LIR.Alt
convertAlt (IR.Alt srcSpan conPat varPats expr) =
  LIR.Alt srcSpan (convertConPat conPat) (map convertVarPat varPats)
    <$> convertExpr expr

convertConPat :: IR.ConPat -> LIR.ConPat
convertConPat (IR.ConPat srcSpan name) = LIR.ConPat srcSpan name

-- translated without fresh ident, because @localEnv@ is not possible in lifted IR!
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

-------------------------------------------------------------------------------
-- Smart Constructors                                                        --
-------------------------------------------------------------------------------

guessName :: LIR.Expr -> Maybe String
guessName (LIR.Var _ name _  ) = IR.identFromQName name
guessName (LIR.Bind _ arg _ _) = guessName arg
guessName _                    = Nothing

bind :: LIR.Expr -> (LIR.Expr -> Converter LIR.Expr) -> Converter LIR.Expr
bind arg k = do
  let argIdent = IR.UnQual $ IR.Ident $ fromMaybe "f" (guessName arg)
  -- argIdent <- freshIRQName $ fromMaybe "f" (guessName arg)
  rhs <- lambda NoSrcSpan [varPat argIdent] <$> k (var argIdent)
  return $ LIR.Bind NoSrcSpan arg rhs undefined

app :: LIR.Expr -> LIR.Expr -> LIR.Expr
app l@(LIR.App _ _ _ _ _ _) r = l { LIR.exprAppArgs = r : LIR.exprAppArgs l } -- TODO: update types ; reverses Args?
app l                       r = LIR.App NoSrcSpan l [] [] [r] undefined

var :: LIR.VarName -> LIR.Expr
var ident = LIR.Var NoSrcSpan ident undefined

varPat :: LIR.VarName -> LIR.VarPat
varPat ident = LIR.VarPat NoSrcSpan ident Nothing

lambda :: SrcSpan -> [LIR.VarPat] -> LIR.Expr -> LIR.Expr
lambda srcSpan args rhs = LIR.Lambda srcSpan args rhs $ LIR.funcType
  NoSrcSpan
  (map (fromJust . LIR.varPatType) args)
  (LIR.exprType rhs)

ite :: SrcSpan -> LIR.Expr -> LIR.Expr -> LIR.Expr -> LIR.Expr
ite srcSpan cond true false =
  LIR.If srcSpan cond true false $ LIR.exprType true

pure :: SrcSpan -> LIR.Expr -> LIR.Expr
pure srcSpan expr =
  LIR.Pure srcSpan expr $ LIR.FreeTypeCon srcSpan $ LIR.exprType expr










