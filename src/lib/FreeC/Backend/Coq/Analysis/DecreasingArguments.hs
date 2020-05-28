-- | This module contains the termination checker for the intermediate
--   language. The goal is to to find one argument for every recursive
--   function whose size is reduced in every recursive call. If such
--   arguments exist we know that the function will terminate and can
--   be translated to Coq. The termination checker defined in this
--   module is very limited compared to Coq's termination checker.
--   Even if we don't recognize the decreasing arguments, Coq might
--   still be able to tell that the function is decreasing on one of
--   its arguments. However, we cannot rely on Coq's termination
--   entirely, since we need to know the decreasing arguments for
--   the transformation of recursive functions into a recursive
--   helper function and a non-recursive main function (see also
--   "FreeC.Backend.Coq.Converter.FuncDecl.Rec.WithHelpers")
--
--   == Guessing Decreasing Arguments
--
--   Given set of mutually recursive function declarations @F@, the
--   termination checker tries to find a combination of arguments such
--   that each function in the set decreases on the corresponding argument.
--   Since we have to know the decreasing argument of all functions in the
--   set in order to test whether a function decreases on one of its argument,
--   we first enumerate (or /guess/) all possible combinations and then check
--   whether the combination of decreasing arguments is valid.
--
--   == Checking Decreasing Arguments
--
--   A function @f ∈ F@ declared by
--
--   > f x₁ … xᵢ … xₙ = e
--
--   decreases on its @i@-th argument if for every recursive call to
--   functions @g ∈ F@ on the right-hand side @e@ of @f@
--
--   > g e₁ … eⱼ … eₘ
--
--   where @j@ is the decreasing argument guessed for @g@ the expression
--   @eⱼ@ is recognizes as structurally smaller than @xᵢ@.
--
--   == Checking for Structurally Smaller Expressions
--
--   Within a function for whose decreasing argument we've guessed @xᵢ@ a
--   variable @x@ is structurally smaller than @xᵢ@ if one of the following
--   two conditions is met.
--
--   1. @x@ is bound by a variable pattern in a @case@ expression whose
--      scrutinee is the decreasing argument @xᵢ@.
--
--   2. @x@ is bound by a variable pattern in a @case@ expression whose
--      scrutinee is structurally smaller that @xᵢ@ itself.
--
--   == Bypassing the termination checker
--
--   Cop's termination checker uses the same idea as described above but
--   is much more sophisticated. If the user knows that their function
--   declaration is decreasing on one of its arguments, they can annotate
--   the decreasing argument using a custom pragma (see also
--   'FreeC.IR.Syntax.Pragma.DecArgPragma'). If there is such an annotation
--   'guessDecArgs' will not consider any other argument for the annotated
--   function declaration and 'checkDecArgs' always accepts the guessed
--   argument as a decreasing argument.

module FreeC.Backend.Coq.Analysis.DecreasingArguments
  ( DecArgIndex
  , identifyDecArgs
  )
where

import           Data.List                      ( find )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Set                       ( Set
                                                , (\\)
                                                )
import qualified Data.Set                      as Set
import           Data.Tuple.Extra               ( uncurry3 )

import           FreeC.Environment
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pretty
import           FreeC.Util.Predicate           ( (.||.) )

-------------------------------------------------------------------------------
-- Guessing Decreasing Arguments                                             --
-------------------------------------------------------------------------------

-- | Type for the index of a decreasing argument.
type DecArgIndex = Int

-- | Guesses all possible combinations of decreasing arguments for the given
--   mutually recursive function declarations.
--
--   The second argument contains the known decreasing arguments as specified
--   by the user.
--
--   Returns a list of all possible combinations of argument indecies.
guessDecArgs :: [IR.FuncDecl] -> [Maybe DecArgIndex] -> [[DecArgIndex]]
guessDecArgs []          _  = return []
guessDecArgs _           [] = return []
guessDecArgs (_ : decls) (Just decArgIndex : knownDecArgIndecies) = do
  decArgIndecies <- guessDecArgs decls knownDecArgIndecies
  return (decArgIndex : decArgIndecies)
guessDecArgs (decl : decls) (Nothing : knownDecArgIndecies) = do
  let arity = length (IR.funcDeclArgs decl)
  decArgIndecies <- guessDecArgs decls knownDecArgIndecies
  decArgIndex    <- [0 .. arity - 1]
  return (decArgIndex : decArgIndecies)

-------------------------------------------------------------------------------
-- Checking Decreasing Arguments                                             --
-------------------------------------------------------------------------------

-- | Tests whether the given combination of choices for the decreasing
--   arguments of function declarations in a strongly connected component
--   is valid (i.e. all function declarations actually decrease the
--   corresponding argument).
--
--   The second argument contains the known decreasing arguments as specified
--   by the user. If the user has specied the decreasing argument of a function
--   it is not checked whether the function actually decreases on the argument
--   (such that the user is not limited by our termination checker).
checkDecArgs :: [IR.FuncDecl] -> [Maybe DecArgIndex] -> [DecArgIndex] -> Bool
checkDecArgs decls knownDecArgIndecies decArgIndecies = all
  (uncurry3 checkDecArg)
  (zip3 knownDecArgIndecies decArgIndecies decls)
 where
  -- | Maps the names of functions in the strongly connected component
  --   to the index of their decreasing argument.
  decArgMap :: Map IR.QName DecArgIndex
  decArgMap =
    foldr (uncurry insertFuncDecl) Map.empty (zip decls decArgIndecies)

  -- | Inserts a function declaration with the given decreasing argument index
  --   into 'decArgMap'.
  insertFuncDecl
    :: IR.FuncDecl
    -> DecArgIndex
    -> Map IR.QName DecArgIndex
    -> Map IR.QName DecArgIndex
  insertFuncDecl = Map.insert . IR.funcDeclQName

  -- | Tests whether the given function declaration actually decreases on the
  --   argument with the given index.
  --
  --   The first argument is the index of the decreasing argument as specified
  --   by the user or @Nothing@ if there is no such annotation.
  checkDecArg :: Maybe DecArgIndex -> DecArgIndex -> IR.FuncDecl -> Bool
  checkDecArg (Just _) _ _ = True
  checkDecArg _ decArgIndex (IR.FuncDecl _ _ _ args _ rhs) =
    let decArg = IR.varPatQName (args !! decArgIndex)
    in  checkExpr decArg Set.empty rhs []

  -- | Tests whether there is a variable that is structurally smaller than the
  --   argument with the given name in the position of decreasing arguments of
  --   all applications of functions from the strongly connected component.
  --
  --   The second argument is a set of variables that are known to be
  --   structurally smaller than the decreasing argument of the function
  --   whose right hand side is checked.
  --
  --   The last argument is a list of actual arguments passed to the given
  --   expression.
  checkExpr :: IR.QName -> Set IR.QName -> IR.Expr -> [IR.Expr] -> Bool
  checkExpr decArg smaller = checkExpr'
   where
    -- | Tests whether the given expression is the decreasing argument.
    isDecArg :: IR.Expr -> Bool
    isDecArg (IR.Var _ varName _) = varName == decArg
    isDecArg _                    = False

    -- | Tests whether the given expression is a structurally smaller
    --   variable than the decreasing argument.
    isSmaller :: IR.Expr -> Bool
    isSmaller (IR.Var _ varName _) = varName `elem` smaller
    isSmaller _                    = False

    -- | Tests whether the given expression matches 'isDecArg' or 'isSmaller'.
    isDecArgOrSmaller :: IR.Expr -> Bool
    isDecArgOrSmaller = isDecArg .||. isSmaller

    -- If one of the recursive functions is applied, there must be a
    -- structurally smaller variable in the decreasing position.
    checkExpr' (IR.Var _ name _) args = case Map.lookup name decArgMap of
      Nothing -> True
      Just decArgIndex | decArgIndex >= length args -> False
                       | otherwise -> isSmaller (args !! decArgIndex)

    -- Function applications and @if@-expressions need to be checked
    -- recursively. In case of applications we also remember the
    -- arguments such that the case above can inspect the actual arguments.
    checkExpr' (IR.App _ e1 e2 _) args =
      checkExpr' e1 (e2 : args) && checkExpr' e2 []
    checkExpr' (IR.If _ e1 e2 e3 _) _ =
      checkExpr' e1 [] && checkExpr' e2 [] && checkExpr' e3 []

    -- @case@-expressions that match the decreasing argument or a variable
    -- that is structurally smaller than the decreasing argument, introduce
    -- new structurally smaller variables.
    checkExpr' (IR.Case _ expr alts _) _
      | isDecArgOrSmaller expr = all checkSmallerAlt alts
      | otherwise              = all checkAlt alts

    -- The arguments of lambda expressions shadow existing (structurally
    -- smaller) variables.
    checkExpr' (IR.Lambda _ args expr _) _ =
      let smaller' = withoutArgs args smaller
      in  checkExpr decArg smaller' expr []

    -- Recursively check visibly applied expressions.
    checkExpr' (IR.TypeAppExpr _ expr _ _) args = checkExpr' expr args

    -- Base expressions don't contain recursive calls.
    checkExpr' (IR.Con _ _ _             ) _    = True
    checkExpr' (IR.Undefined _ _         ) _    = True
    checkExpr' (IR.ErrorExpr  _ _ _      ) _    = True
    checkExpr' (IR.IntLiteral _ _ _      ) _    = True

    -- | Applies 'checkExpr' on the right hand side of an alternative of a
    --   @case@ expression.
    --
    --   The variable patterns shadow existing (structurally smaller) variables
    --   with the same name.
    checkAlt :: IR.Alt -> Bool
    checkAlt (IR.Alt _ _ varPats expr _) =
      let smaller' = withoutArgs varPats smaller
      in  checkExpr decArg smaller' expr []

    -- | Like 'checkAlt' but for alternatives of @case@-expressions on
    --   the decreasing argument or a variable that is structurally smaller.
    --
    --   All variable patterns are added to the set of structurally smaller
    --   variables.
    checkSmallerAlt :: IR.Alt -> Bool
    checkSmallerAlt (IR.Alt _ _ varPats expr _) =
      let smaller' = withArgs varPats smaller
      in  checkExpr decArg smaller' expr []

    -- | Adds the given variables to the set of structurally smaller variables.
    withArgs :: [IR.VarPat] -> Set IR.QName -> Set IR.QName
    withArgs args set = set `Set.union` Set.fromList (map IR.varPatQName args)

    -- | Removes the given variables to the set of structurally smaller
    --   variables (because they are shadowed by an argument from a lambda
    --   abstraction or @case@-alternative).
    withoutArgs :: [IR.VarPat] -> Set IR.QName -> Set IR.QName
    withoutArgs args set = set \\ Set.fromList (map IR.varPatQName args)

-------------------------------------------------------------------------------
-- Identifying Decreasing Arguments                                          --
-------------------------------------------------------------------------------

-- | Identifies the decreasing arguments of the given mutually recursive
--   function declarations.
--
--   The second argument contains the known decreasing arguments as specified
--   by the user.
--
--   Returns @Nothing@ if the decreasing argument could not be identified.
maybeIdentifyDecArgs
  :: [IR.FuncDecl] -> [Maybe DecArgIndex] -> Maybe [DecArgIndex]
maybeIdentifyDecArgs decls knownDecArgIndecies = find
  (checkDecArgs decls knownDecArgIndecies)
  (guessDecArgs decls knownDecArgIndecies)

-- | Identifies the decreasing arguments of the given mutually recursive
--   function declarations.
--
--   Reports a fatal error message, if the decreasing arguments could not be
--   identified.
identifyDecArgs :: [IR.FuncDecl] -> Converter [DecArgIndex]
identifyDecArgs decls = do
  knownDecArgIndecies <- mapM lookupDecArgIndexOfDecl decls
  maybe decArgError return (maybeIdentifyDecArgs decls knownDecArgIndecies)
 where
  -- | Looks up the index of an annotated decreasing argument.
  lookupDecArgIndexOfDecl :: IR.FuncDecl -> Converter (Maybe Int)
  lookupDecArgIndexOfDecl = inEnv . lookupDecArgIndex . IR.funcDeclQName

  -- | Prints an error message if the decreasing arguments could not
  --   be identified.
  decArgError :: Converter a
  decArgError =
    reportFatal
      $  Message (IR.funcDeclSrcSpan (head decls)) Error
      $  "Could not identify decreasing arguments of "
      ++ showPretty (map IR.funcDeclIdent decls)
      ++ ".\n"
      ++ "Consider adding a "
      ++ "{-# FreeC <function> DECREASES ON <argument> #-} "
      ++ "annotation."
