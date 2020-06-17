-- | This module contains a compiler pass that checks if all function
--   declarations have complete pattern matching. A pattern is complete if there
--   is exactly one case alternative for each constructor of the corresponding
--   type.
--
--   = Examples
--
--   == Example 1
--
--   The module consisting of the following declarations
--
--   > data Maybe a = Just a | Nothing
--   >
--   > fromJust :: Maybe a -> a
--   > fromJust @a (x :: Maybe a) = case (x :: Maybe a) of {Just a -> a}
--
--   should not pass the check because the @case@ expression is missing an
--   alternative for the constructor @Nothing@.
--
--   == Example 2
--
--   The following declaration with redundant alternatives
--
--   > redundant :: Just Bool -> Just Bool
--   > redundant (on :: Just Bool) = case (on :: Just Bool) of {
--   >     Just a  -> Just False;
--   >     Nothing -> Nothing;
--   >     Just b  -> Just True
--   >   }
--
--   should not pass the check because the @case@ expression has two alternatives
--   for the constructor @Just@.
--
--   == Example 3
--
--   The following declaration where the scrutinee is a function
--
--   > case_id = case \x -> x  of
--
--   should not pass the check because functions are not permitted as scrutinees.
--
--   = Specification
--
--   == Preconditions
--
--   The type of all checked expressions has to be annotated.
--   The environment has to contain the names of all constructors for
--   all used data types.
--   Additionally, the environment should contain entries for all used type
--   synonyms.
--
--   == Translation
--
--   This pass only performs a check and therefore does not change the module.
--
--   == Postconditions
--
--   All case expressions are guaranteed to have complete pattern matching.
--
--   == Error cases
--
--   A fatal error is reported if an incomplete case expression is found.

module FreeC.Pass.CompletePatternPass
  ( completePatternPass
  , checkPatternFuncDecl
  )
where

import           Control.Monad                  ( unless )
import           Data.Maybe                     ( fromJust )

import           FreeC.Environment.Entry
import           FreeC.Environment.LookupOrFail
import qualified FreeC.IR.Syntax               as IR
import           FreeC.IR.SrcSpan
import           FreeC.IR.TypeSynExpansion
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pass
import           FreeC.Pretty                   ( showPretty )

-- | Checks that all functions of a given module have complete pattern matching.
--
--   The pattern matching for a function is complete if for each @case@
--   expression there exists exactly one case alternative for each constructor
--   of the corresponding type.
completePatternPass :: Pass IR.Module
completePatternPass ast = do
  mapM_ checkPatternFuncDecl (IR.modFuncDecls ast)
  return ast

-- | Checks a function declaration for incomplete patterns.
checkPatternFuncDecl :: IR.FuncDecl -> Converter ()
checkPatternFuncDecl funcDecl = checkPatternExpr (IR.funcDeclRhs funcDecl)
 where
  -- | Checks an expression for incomplete patterns.
  checkPatternExpr :: IR.Expr -> Converter ()
  checkPatternExpr (IR.Case srcSpan exprScrutinee exprAlts _) = do
    checkPatternExpr exprScrutinee
    mapM_ (checkPatternExpr . IR.altRhs) exprAlts
    -- The usage of 'fromJust' is safe, because all types are annotated.
    let tau = fromJust $ IR.exprType exprScrutinee
    tau' <- expandAllTypeSynonyms tau
    case getTypeConName tau' of
      Nothing       -> failedPatternCheck srcSpan
      Just typeName -> do
        -- If an entry is found we can assume that it is 'DataEntry' because
        -- all type synonyms have been expanded.
        entry <- lookupEntryOrFail srcSpan IR.TypeScope typeName
        let altConNames = map (IR.conPatName . IR.altConPat) exprAlts
        performCheck (entryConsNames entry) altConNames srcSpan
  checkPatternExpr (IR.App _ lhr rhs _) =
    checkPatternExpr lhr >> checkPatternExpr rhs
  checkPatternExpr (IR.TypeAppExpr _ lhr _ _) = checkPatternExpr lhr
  checkPatternExpr (IR.If _ exprCond exprThen exprElse _) =
    checkPatternExpr exprCond
      >> checkPatternExpr exprThen
      >> checkPatternExpr exprElse
  checkPatternExpr (IR.Lambda _ _ lambdaRhs _) = checkPatternExpr lambdaRhs
  checkPatternExpr IR.Con{}                    = return ()
  checkPatternExpr IR.Var{}                    = return ()
  checkPatternExpr IR.Undefined{}              = return ()
  checkPatternExpr IR.ErrorExpr{}              = return ()
  checkPatternExpr IR.IntLiteral{}             = return ()

  performCheck :: [IR.ConName] -> [IR.ConName] -> SrcSpan -> Converter ()
  performCheck typeConNames altConNames srcSpan = unless
    (  all (`elem` typeConNames) typeConNames
    && length typeConNames
    == length altConNames
    )
    (failedPatternCheck srcSpan)

  -- | Generates the error message and reports the error
  failedPatternCheck :: SrcSpan -> Converter ()
  failedPatternCheck srcSpan =
    reportFatal
      $  Message srcSpan Error
      $  "Incomplete pattern in function: "
      ++ showPretty (IR.funcDeclName funcDecl)

  -- | Selects the name of the outermost type constructor from a type
  getTypeConName :: IR.Type -> Maybe IR.TypeConName
  getTypeConName (IR.TypeCon _ typeConName ) = Just typeConName
  getTypeConName (IR.TypeApp _ typeAppLhs _) = getTypeConName typeAppLhs

  -- The type of the scrutinee shouldn't be function or a type var
  getTypeConName IR.TypeVar{}                = Nothing
  getTypeConName IR.FuncType{}               = Nothing
