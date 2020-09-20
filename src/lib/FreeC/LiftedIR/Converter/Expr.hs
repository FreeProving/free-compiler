{-# LANGUAGE TupleSections #-}

-- | Implements the IR to lifted IR translation for expressions.
module FreeC.LiftedIR.Converter.Expr ( liftExpr ) where

import           Control.Applicative            ( (<|>) )
import           Control.Monad                  ( join, when )
import           Data.Bool                      ( bool )
import           Data.Foldable
import           Data.Maybe                     ( fromJust, fromMaybe )

import           FreeC.Environment
import           FreeC.Environment.Entry        ( entryAgdaIdent, entryIdent )
import           FreeC.Environment.Fresh
import           FreeC.Environment.LookupOrFail
  ( lookupAgdaFreshIdentOrFail, lookupAgdaValIdentOrFail, lookupIdentOrFail )
import           FreeC.Environment.Renamer      ( renameAndDefineLIRVar )
import qualified FreeC.IR.Base.Prelude          as IR.Prelude
import           FreeC.IR.SrcSpan               ( SrcSpan(NoSrcSpan) )
import           FreeC.IR.Subst
import qualified FreeC.IR.Syntax                as IR
import           FreeC.IR.Syntax.Name           ( identFromQName )
import qualified FreeC.LiftedIR.Converter.Type  as LIR
import           FreeC.LiftedIR.Effect
import qualified FreeC.LiftedIR.Syntax          as LIR
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
  ( Message(Message), Severity(Internal), reportFatal )
import           FreeC.Pretty                   ( showPretty )

-- | Converts an expression from IR to lifted IR and lifts it during the
--   translation.
liftExpr :: IR.Expr -> Converter LIR.Expr
liftExpr expr = liftExpr' expr [] []

-- | Same as @liftExpr@ but accumulates arguments.
--
--   This function always produces a term of type @Free S P τ*@.
--   The accumulation of arguments is needed to reason about fully applied
--   functions. Top level functions and constructors are lifted argument wise.
--   Translating them without considering all arguments would violate the
--   invariant.
--
--   > e : τ ↦ e' : τ'
liftExpr' :: IR.Expr -> [IR.Type] -> [IR.Expr] -> Converter LIR.Expr

-- Pass argument from applications to converter for callee, allowing us to
-- convert functions and constructors with full access to their parameters.
--
-- >             $
-- > liftExpr'  / \   [] args = liftExpr' e₁ [] (e₂ : args)
-- >           e₁  e₂
liftExpr' (IR.App _ e1 e2 _) [] args = liftExpr' e1 [] (e2 : args)
-- Pass type argument from visible type application to converter for callee.
--
-- >             @
-- > liftExpr'  / \   tArgs args = liftExpr' e (τ : tArgs) args
-- >           e   τ
liftExpr' (IR.TypeAppExpr _ e t _) typeArgs args = liftExpr' e (t : typeArgs)
  args
-- Constructors.
liftExpr' (IR.Con srcSpan name _) typeArgs args = do
  args' <- mapM liftExpr args
  typeArgs' <- mapM LIR.liftType' typeArgs
  Just typeArgArity <- inEnv $ lookupTypeArgArity IR.ValueScope name
  let con          = LIR.SmartCon srcSpan name
      typeArgCount = length typeArgs'
  when (typeArgCount /= typeArgArity)
    $ reportFatal
    $ Message srcSpan Internal
    $ unlines [ "The constructor '"
                  ++ showPretty name
                  ++ "' is applied to the wrong number of type arguments."
              , "Expected "
                  ++ show typeArgArity
                  ++ " type arguments, got "
                  ++ show typeArgCount
                  ++ "."
              ]
  return $ LIR.App srcSpan con typeArgs' [] args' True
-- Cases for (possible applied) variables (i.e. variables and functions).
liftExpr' (IR.Var srcSpan name _) typeArgs args = do
  args' <- mapM liftExpr args
  agdaIdent <- lookupAgdaValIdentOrFail srcSpan name
  coqIdent <- lookupIdentOrFail srcSpan IR.ValueScope name
  let varName      = LIR.Var srcSpan name agdaIdent coqIdent
      typeArgCount = length typeArgs
  maybeTypeArgArity <- inEnv $ lookupTypeArgArity IR.ValueScope name
  -- The number of type arguments must match the number of type parameters.
  -- In case of variables, there must be no type arguments.
  -- Since, the user cannot create visible type applications, it is an
  -- internal error if the number of type arguments does not match.
  case maybeTypeArgArity of
    Just typeArgArity -> when (typeArgCount /= typeArgArity)
      $ reportFatal
      $ Message srcSpan Internal
      $ unlines [ "The function '"
                    ++ showPretty name
                    ++ "' is applied to the wrong number of type arguments."
                , "Expected "
                    ++ show typeArgArity
                    ++ " type arguments, got "
                    ++ show typeArgCount
                    ++ "."
                ]
    Nothing           -> when (typeArgCount /= 0)
      $ reportFatal
      $ Message srcSpan Internal
      $ unlines [ "The variable '"
                    ++ showPretty name
                    ++ "' must not be applied to type arguments."
                , "Got " ++ show typeArgCount ++ " type arguments."
                ]
  function <- inEnv $ isFunction name
  if function -- If this is a top level functions it's lifted argument wise.
    then do
      effects <- inEnv $ lookupEffects name
      Just strictArgs <- inEnv $ lookupStrictArgs name
      freeArgs <- inEnv $ needsFreeArgs name
      Just typeArgIdents <- inEnv $ lookupTypeArgs IR.ValueScope name
      Just argTypes <- inEnv $ lookupArgTypes IR.ValueScope name
      Just arity <- inEnv $ lookupArity IR.ValueScope name
      let typeArgNames = map (IR.UnQual . IR.Ident) typeArgIdents
          subst        = composeSubsts
            (zipWith singleSubst typeArgNames typeArgs)
      argTypes' <- mapM (LIR.liftType' . applySubst subst) argTypes
      typeArgs' <- mapM LIR.liftType' typeArgs
      generateBinds (zip3 args' (map Just argTypes' ++ repeat Nothing)
                     $ strictArgs ++ repeat False)
        $ \args'' -> generateApply
        (LIR.App srcSpan varName typeArgs' effects (take arity args'') freeArgs)
        $ drop arity args''
    else do
      pureArg <- inEnv $ isPureVar name
      generateApply (bool id (LIR.Pure NoSrcSpan) pureArg varName) args'
-- Integer Literals.
liftExpr' (IR.IntLiteral srcSpan value _) [] []
  = return $ LIR.Pure srcSpan $ LIR.IntLiteral srcSpan value
-- Lambda abstractions.
--
-- > (\(x :: τ) -> e)' = pure (\(x :: τ') -> e')
liftExpr' (IR.Lambda srcSpan args rhs _) [] [] = localEnv $ do
  (pats, expr) <- liftAlt' args rhs
  return
    $ foldr (\a b -> LIR.Pure srcSpan $ LIR.Lambda srcSpan [a] b) expr pats
-- @if@-expressions.
--
-- > (if e₁ then e₂ else e₃)'
-- >   = e₁' >>= \(x :: Bool Shape Pos) -> if x then e₂' else e₃'
--
-- Note that the argument of the lambda is lifted, but its type is
-- @Bool Shape Pos@, which is just an alias for @bool@, which ignores its
-- arguments.
liftExpr' (IR.If srcSpan cond true false _) [] [] = do
  cond' <- liftExpr cond
  bool' <- LIR.liftType' $ IR.TypeCon NoSrcSpan IR.Prelude.boolTypeConName
  bind cond' freshBoolPrefix (Just bool')
    $ \d -> LIR.If srcSpan d <$> liftExpr true <*> liftExpr false
-- @case@-expressions.
--
-- > (case (e :: τ) of alts)' = e' >>= \(x :: τ*) -> case x of alts'
--
-- where @alts'@ are the lifted (not smart) constructors for τ₀.
liftExpr' (IR.Case srcSpan discriminante patterns _) [] [] = do
  discriminant' <- liftExpr discriminante
  bind discriminant' freshArgPrefix Nothing
    $ \d -> LIR.Case srcSpan d <$> mapM liftAlt patterns
liftExpr' (IR.Undefined srcSpan _) typeArgs args = do
  when (length typeArgs /= 1)
    $ reportFatal
    $ Message srcSpan Internal
    $ unlines
    [ "Error term 'undefined' is applied to the wrong number of type arguments."
    , "Expected 1 type arguments, got " ++ show (length typeArgs) ++ "."
    ]
  typeArgs' <- mapM LIR.liftType' typeArgs
  args' <- mapM liftExpr args
  generateApply
    (LIR.App srcSpan (LIR.Undefined srcSpan) typeArgs' [Partiality] [] True)
    args'
liftExpr' (IR.ErrorExpr srcSpan msg _) typeArgs args = do
  when (length typeArgs /= 1)
    $ reportFatal
    $ Message srcSpan Internal
    $ unlines
    [ "Error term 'error "
        ++ show msg
        ++ "' is applied to the wrong number of type arguments."
    , "Expected 1 type arguments, got " ++ show (length typeArgs) ++ "."
    ]
  typeArgs' <- mapM LIR.liftType' typeArgs
  args' <- mapM liftExpr args
  generateApply (LIR.App srcSpan (LIR.ErrorExpr srcSpan) typeArgs' [Partiality]
                 [LIR.StringLiteral srcSpan msg] True) args'
liftExpr' (IR.Let _ binds expr _) [] [] = liftBinds binds expr
-- Visible type application of an expression other than a function or
-- constructor.
liftExpr' expr (_ : _) _ = reportFatal
  $ Message (IR.exprSrcSpan expr) Internal
  $ "Only type arguments of functions and constructors can be applied visibly."
-- Application of an expression other than a function or constructor
-- application. We use an as-pattern for @args@ such that we get a compile
-- time warning when a node is added to the AST that we do not cover above.
liftExpr' expr [] args@(_ : _)
  = join $ generateApply <$> liftExpr expr <*> mapM liftExpr args

-------------------------------------------------------------------------------
-- Lift Patterns                                                             --
-------------------------------------------------------------------------------
-- | Translates a constructor pattern from IR to LIR.
liftConPat :: IR.ConPat -> LIR.ConPat
liftConPat (IR.ConPat srcSpan name) = LIR.ConPat srcSpan name

-- | Translates a case alternative pattern from IR to LIR, by lifting the
--   pattern and the right-hand side.
liftAlt :: IR.Alt -> Converter LIR.Alt
liftAlt (IR.Alt srcSpan conPat pats expr) = do
  (pats', expr') <- liftAlt' pats expr
  return $ LIR.Alt srcSpan (liftConPat conPat) pats' expr'

-- | Translates an alternative (which consist of a list of variable patterns and
--   a bound expression). Strict variables are replaced with fresh ones, which
--   are unwrapped using @>>=@.
liftAlt' :: [IR.VarPat] -> IR.Expr -> Converter ([LIR.VarPat], LIR.Expr)
liftAlt' [] expr = ([], ) <$> liftExpr expr
liftAlt' (pat@(IR.VarPat srcSpan name varType strict) : pats) expr
  = localEnv $ do
    varType' <- LIR.liftVarPatType pat
    var <- renameAndDefineLIRVar srcSpan strict name varType
    (pats', expr') <- liftAlt' pats expr
    if strict then do
      var' <- freshIRQName name
      expr'' <- rawBind srcSpan var' var varType expr'
      pat' <- makeVarPat srcSpan var' varType'
      return (pat' : pats', expr'') else do
      pat' <- makeVarPat srcSpan var varType'
      return (pat' : pats', expr')

-- | Smart constructor for variable patterns.
makeVarPat :: SrcSpan -> IR.QName -> Maybe LIR.Type -> Converter LIR.VarPat
makeVarPat srcSpan var varType = do
  let Just unqualVar = identFromQName var
  valueEntry <- inEnv $ lookupEntry IR.ValueScope var
  freshEntry <- inEnv $ lookupEntry IR.FreshScope var
  let agdaVar = entryAgdaIdent $ fromJust (valueEntry <|> freshEntry)
  let coqVar = entryIdent $ fromJust (valueEntry <|> freshEntry)
  return $ LIR.VarPat srcSpan unqualVar varType agdaVar coqVar

-------------------------------------------------------------------------------
-- Application Expression Helper                                             --
-------------------------------------------------------------------------------
-- | Applies a n-ary lifted function by applying the rule below repeatedly.
--
--   > ⎡Γ ⊢ e₀:τ₀ → τ₁   Γ ⊢ e₁:τ₀⎤'  Γ' ⊢ e₀' : m(τ₀' → τ₁')    Γ' ⊢ e₁':τ₀'
--   > ⎢--------------------------⎥ = ---------------------------------------
--   > ⎣      Γ ⊢ e₀e₁ : τ₁       ⎦   Γ' ⊢ e₀' >>= λf:(τ₀' → τ₁').f e₀' : e₁'
generateApply :: LIR.Expr -> [LIR.Expr] -> Converter LIR.Expr
generateApply = foldlM $ \expr arg -> bind expr freshFuncPrefix Nothing
  $ \f -> return $ LIR.App NoSrcSpan f [] [] [arg] False

-------------------------------------------------------------------------------
-- Bind Expression                                                           --
-------------------------------------------------------------------------------
-- | Tries to extract a variable name from an expression. This function can be
--   used to preserve the same base variable name across chains of binds.
guessName :: LIR.Expr -> Maybe String
guessName (LIR.Var _ name _ _) = IR.identFromQName name
guessName (LIR.Pure _ arg)     = guessName arg
guessName (LIR.Bind _ arg _)   = guessName arg
guessName _                    = Nothing

-- | Creates a @>>= \x ->@, which binds a new variable.
bind :: LIR.Expr -- ^ The left-hand side of the bind.
     -> String   -- ^ A prefix to use for the fresh variable by default.
     -> Maybe LIR.Type
     -- ^ The type of the value to bind or @Nothing@ if it should be inferred.
     -> (LIR.Expr -> Converter LIR.Expr)
     -- ^ Converter for the right-hand side of the generated
     --   function. The first argument is the fresh variable.
     -> Converter LIR.Expr
bind (LIR.Pure _ arg) _ _ k      = k arg -- We don't have to unwrap pure values.
bind arg defaultPrefix argType k = localEnv $ do
  -- Generate a new name for lambda argument.
  argIdent <- freshIRQName $ fromMaybe defaultPrefix (guessName arg)
  let Just argIdent' = identFromQName argIdent
  -- Build the lambda on the RHS of the bind.
  argAgda <- lookupAgdaFreshIdentOrFail NoSrcSpan argIdent
  argCoq <- lookupIdentOrFail NoSrcSpan IR.FreshScope argIdent
  let pat = LIR.VarPat NoSrcSpan argIdent' argType argAgda argCoq
  rhs <- LIR.Lambda NoSrcSpan [pat]
    <$> k (LIR.Var NoSrcSpan argIdent argAgda argCoq)
  -- Build the bind.
  return $ LIR.Bind NoSrcSpan arg rhs

-- | Passes a list of arguments to the given function unwrapping the marked
--   arguments using 'bind'.
generateBinds :: [(LIR.Expr, Maybe LIR.Type, Bool)]
              -> ([LIR.Expr] -> Converter LIR.Expr)
              -> Converter LIR.Expr
generateBinds [] k = k []
generateBinds ((arg, _, False) : as) k = generateBinds as $ \as' -> k
  (arg : as')
generateBinds ((arg, argType, True) : as) k = bind arg freshArgPrefix argType
  $ \arg' -> generateBinds as $ \as' -> k (arg' : as')

-- | Generates just the syntax for a bind expression, which unwraps the first
--   variable and binds its value to the second one in the given expression.
rawBind :: SrcSpan   -- ^ The source location of the bind.
        -> IR.QName  -- ^ The variable on the left-hand side of the bind.
        -> IR.QName  -- ^ The variable in the lambda expression.
        -> Maybe IR.Type
        -- ^ The type annotation of the variable in the lambda expression or
        --   @Nothing@ if no annotation should be generated.
        -> LIR.Expr  -- ^ The right-hand side of the bind.
        -> Converter LIR.Expr
rawBind srcSpan mx x varType expr = do
  mxAgda <- lookupAgdaFreshIdentOrFail srcSpan mx
  mxCoq <- lookupIdentOrFail srcSpan IR.FreshScope mx
  xAgda <- lookupAgdaValIdentOrFail srcSpan x
  xCoq <- lookupIdentOrFail srcSpan IR.ValueScope x
  varType' <- mapM LIR.liftType' varType
  let mx'          = LIR.Var srcSpan mx mxAgda mxCoq
      Just unqualX = identFromQName x
      x'           = LIR.VarPat srcSpan unqualX varType' xAgda xCoq
  return $ LIR.Bind srcSpan mx' $ LIR.Lambda srcSpan [x'] expr

-------------------------------------------------------------------------------
-- Let Expression Helper                                                     --
-------------------------------------------------------------------------------
-- | Lifts a list of let bindings.
--
--   The given expression is the right-hand side of the let.
liftBinds :: [IR.Bind] -> IR.Expr -> Converter LIR.Expr
liftBinds [] expr = liftExpr expr
liftBinds ((IR.Bind srcSpan varPat bindExpr) : bs) expr = localEnv $ do
  let (IR.VarPat patSrcSpan ident varPatType isStrict) = varPat
  _ <- renameAndDefineLIRVar srcSpan isStrict ident varPatType
  expr' <- liftBinds bs expr
  patType' <- mapM LIR.liftType varPatType
  varPat' <- makeVarPat patSrcSpan (IR.varPatQName varPat) patType'
  shareType' <- mapM LIR.liftType' varPatType
  bindExpr' <- liftExpr bindExpr
  let varName    = IR.varPatQName varPat
      countExprs = expr : map IR.bindExpr bs
      count      = sum (map (countVarInExpr varName) countExprs)
      shareOp    | count > 1 = LIR.Share
                 | otherwise = LIR.Call
      shareExpr  = shareOp srcSpan bindExpr' shareType'
  return $ LIR.Bind srcSpan shareExpr (LIR.Lambda srcSpan [varPat'] expr')

-- | Counts the number of times the variable with the given qualified name
--   occurs in the given expression.
countVarInExpr :: IR.QName -> IR.Expr -> Int
countVarInExpr varName = countVarInExpr'
 where
  countVarInExpr' :: IR.Expr -> Int
  countVarInExpr' IR.Con {}             = 0
  countVarInExpr' (IR.Var _ varName' _) | varName == varName' = 1
                                        | otherwise = 0
  countVarInExpr' (IR.App _ lhs rhs _)
    = countVarInExpr' lhs + countVarInExpr' rhs
  countVarInExpr' (IR.TypeAppExpr _ lhs _ _)   = countVarInExpr' lhs
  countVarInExpr' (IR.If _ cond true false _)
    = countVarInExpr' cond + countVarInExpr' true `max` countVarInExpr' false
  countVarInExpr' (IR.Case _ expr alts _)      = countVarInExpr' expr
    + maximum
    (map (\(IR.Alt _ _ varPats rhs) -> countVarInBinds varPats rhs) alts)
  countVarInExpr' IR.Undefined {}              = 0
  countVarInExpr' IR.ErrorExpr {}              = 0
  countVarInExpr' IR.IntLiteral {}             = 0
  countVarInExpr' (IR.Lambda _ varPats expr _) = countVarInBinds varPats expr
  countVarInExpr' (IR.Let _ binds expr _)      = countVarInExpr' expr
    + sum (map (countVarInExpr' . IR.bindExpr) binds)

  -- | Returns the number of all occurrences of the variable with the given name
  --   in the given expression.
  --
  --   Returns @0@ if the variable occurs in the given variable patterns.
  countVarInBinds :: [IR.VarPat] -> IR.Expr -> Int
  countVarInBinds varPats exprs
    | varPat `elem` map IR.varPatQName varPats = 0
    | otherwise = countVarInExpr varPat exprs
