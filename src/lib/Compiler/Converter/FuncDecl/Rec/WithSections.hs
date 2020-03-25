-- | This module contains functions for converting mutually recursive
--   functions with constant arguments by moving the constant arguments
--   into a @Section@ sentence.
--
--   A @Section@ sentence must be used in case of higher-order functions
--   to tell Coq that the function does not change. Otherwise Coq cannot
--   determine that functions using higher order functions terminate in
--   some cases.

module Compiler.Converter.FuncDecl.Rec.WithSections
  ( convertRecFuncDeclsWithSection
  )
where

import           Control.Monad                  ( mapAndUnzipM
                                                , zipWithM
                                                )
import           Control.Monad.Extra            ( ifM )
import           Data.List                      ( elemIndex
                                                , intercalate
                                                , (\\)
                                                )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Maybe                     ( catMaybes
                                                , fromJust
                                                , fromMaybe
                                                , maybeToList
                                                )
import qualified Data.Set                      as Set

import           Compiler.Analysis.DependencyExtraction
                                                ( typeVarSet
                                                , varSet
                                                )
import           Compiler.Analysis.RecursionAnalysis
import           Compiler.Converter.Free
import           Compiler.Converter.FuncDecl.Common
import           Compiler.Converter.FuncDecl.Rec.WithHelpers
import           Compiler.Converter.Type
import qualified Compiler.Coq.AST              as G
import qualified Compiler.Coq.Base             as CoqBase
import           Compiler.Environment
import           Compiler.Environment.Entry
import           Compiler.Environment.Fresh
import           Compiler.Environment.LookupOrFail
import           Compiler.Environment.Renamer
import           Compiler.Environment.Resolver
import           Compiler.Environment.Scope
import qualified Compiler.Haskell.AST          as HS
import           Compiler.Haskell.Inliner
import           Compiler.Haskell.SrcSpan
import           Compiler.Haskell.Subst
import           Compiler.Haskell.Unification
import           Compiler.Monad.Converter
import           Compiler.Monad.Reporter
import           Compiler.Pretty

-- | Converts recursive function decarations and adds a @Section@ sentence
--   for the given constant arguments.
convertRecFuncDeclsWithSection
  :: [ConstArg] -> [HS.FuncDecl] -> Converter [G.Sentence]
convertRecFuncDeclsWithSection constArgs decls = do
  -- Rename the function declarations in the section.
  (renamedDecls, nameMap) <- renameFuncDecls decls
  let renamedConstArgs = map (renameConstArg nameMap) constArgs
      renamedTypeArgs =
        map (map HS.typeVarDeclIdent . HS.funcDeclTypeArgs) renamedDecls

  -- Lookup the argument and return types of all function declarations.
  (argTypeMaps, returnTypeMaps) <- mapAndUnzipM argAndReturnTypeMaps
                                                renamedDecls
  let argTypeMap    = Map.unions argTypeMaps
      returnTypeMap = Map.unions returnTypeMaps

  -- Unify the argument and return types such that type variable names are
  -- unique.
  (constArgTypes, mgus) <- mapAndUnzipM (lookupConstArgType argTypeMap)
                                        renamedConstArgs
  let mgu           = composeSubsts mgus
      typeArgNames  = Set.toList (Set.unions (map typeVarSet constArgTypes))
      typeArgIdents = map (fromJust . HS.identFromQName) typeArgNames

  -- Apply unificator to rename the type arguments on the right-hand side.
  renamedDecls' <- mapM (applySubst mgu) renamedDecls

  -- Remove constant arguments from the renamed function declarations.
  sectionDecls  <- mapM (removeConstArgsFromFuncDecl renamedConstArgs)
                        renamedDecls'

  -- Test which of the constant arguments is actually used by any function
  -- in the section and which of the type arguments is needed by the types
  -- of used arguments.
  let isConstArgUsed = map (flip any sectionDecls . isConstArgUsedBy) constArgs
      usedConstArgTypes =
        map snd $ filter fst $ zip isConstArgUsed constArgTypes
      isTypeArgUsed v =
        any (Set.member (HS.UnQual (HS.Ident v)) . typeVarSet) usedConstArgTypes
      usedTypeArgIdents = filter isTypeArgUsed typeArgIdents

    -- Remove constant arguments from the type signatures of the renamed
    -- function declarations.
  removedConstTypeArgs <- mapM
    (updateTypeSig mgu usedTypeArgIdents argTypeMap returnTypeMap)
    sectionDecls

  -- Remove visible type applications for type arguments that have been
  -- removed from the type signatures.
  sectionDecls' <- mapM (removeConstTypeArgsFromFuncDecl removedConstTypeArgs)
                        sectionDecls

  -- Generate @Section@ sentence.
  section <- localEnv $ do
    -- Create a @Variable@ sentence for the constant arguments and their type
    -- variables. No @Variable@ sentence is created if a constant argument is
    -- never used (Coq would ignore the @Variable@ sentence anyway).
    maybeTypeArgSentence <- generateConstTypeArgSentence usedTypeArgIdents
    varSentences         <- zipWithM
      generateConstArgVariable
      (map fst $ filter snd $ zip renamedConstArgs isConstArgUsed)
      (map fst $ filter snd $ zip constArgTypes isConstArgUsed)

    -- Generate a section identifier from the names of the original functions
    -- and convert the renamed functions as usual.
    let funcNames  = map HS.funcDeclQName decls
        funcIdents = catMaybes (map HS.identFromQName funcNames)
    sectionIdent <- freshCoqIdent (intercalate "_" ("section" : funcIdents))
    (helperDecls', mainDecls') <- sectionEnv
      $ convertRecFuncDeclsWithHelpers' sectionDecls'
    return
      (G.SectionSentence
        (G.Section
          (G.ident sectionIdent)
          (G.comment ("Constant arguments for " ++ intercalate ", " funcIdents)
          :  genericArgVariables
          ++ maybeToList maybeTypeArgSentence
          ++ varSentences
          ++ G.comment
               ("Helper functions for " ++ intercalate ", " funcIdents)
          :  helperDecls'
          ++ G.comment ("Main functions for " ++ intercalate ", " funcIdents)
          :  mainDecls'
          )
        )
      )

  -- Add functions with correct argument order after the section.
  interfaceDecls' <- zipWithM
    (generateInterfaceDecl constArgs
                           isConstArgUsed
                           nameMap
                           mgu
                           usedTypeArgIdents
    )
    renamedTypeArgs
    decls
  return (section : interfaceDecls')

-------------------------------------------------------------------------------
-- Renaming functions, arguments and type variables                          --
-------------------------------------------------------------------------------

-- | Renames the given function declarations using fresh identifiers.
--
--   The type signatues and environment entries are copied from the
--   original function.
--
--   Fresh identifiers are also generated for type variables in the type
--   signatures.
--
--   Returns the renamed function declarations and a map from old names
--   to new names.
renameFuncDecls
  :: [HS.FuncDecl] -> Converter ([HS.FuncDecl], Map HS.QName HS.QName)
renameFuncDecls decls = do
  -- Create a substitution from old identifiers to fresh identifiers.
  let names = map HS.funcDeclQName decls
  names' <- mapM freshHaskellQName names
  let nameMap = zip names names'
      subst   = composeSubsts $ do
        (name, name') <- nameMap
        return (singleSubst' name (flip HS.untypedVar name'))
  -- Rename function declarations, apply substituion to right-hand side
  -- and copy type signature and entry of original function.
  decls' <-
    flip mapM decls
      $ \(HS.FuncDecl srcSpan (HS.DeclIdent srcSpan' name) typeArgs args rhs maybeRetType) ->
          do
            let Just name'    = lookup name nameMap

            -- Generate fresh identifiers for type variables.
            let typeArgIdents = map HS.typeVarDeclIdent typeArgs
            typeArgIdents' <- mapM freshHaskellIdent typeArgIdents
            let typeArgs' = zipWith HS.TypeVarDecl
                                    (map HS.typeVarDeclSrcSpan typeArgs)
                                    typeArgIdents'
                typeVarSubst = composeSubsts
                  (zipWith singleSubst'
                           (map (HS.UnQual . HS.Ident) typeArgIdents)
                           (map (flip HS.TypeVar) typeArgIdents')
                  )
            args'         <- mapM (applySubst typeVarSubst) args
            maybeRetType' <- mapM (applySubst typeVarSubst) maybeRetType

            -- Set environment entry for renamed function.
            entry         <- lookupEntryOrFail srcSpan' ValueScope name
            _             <- renameAndAddEntry entry
              { entryName       = name'
              , entryTypeArgs   = typeArgIdents'
              , entryArgTypes   = map HS.varPatType args'
              , entryReturnType = maybeRetType'
              }

            -- If the decreasing argument of the original function has been
            -- annotated, copy that annotation.
            maybeDecArg <- inEnv $ lookupDecArg name
            case maybeDecArg of
              Just (decArgIndex, decArgIdent) ->
                modifyEnv $ defineDecArg name' decArgIndex decArgIdent
              Nothing -> return ()

            -- Rename function references and type variables on right-hand side.
            rhs' <- applySubst subst rhs >>= applySubst typeVarSubst

            -- Rename function declaration.
            return
              (HS.FuncDecl srcSpan
                           (HS.DeclIdent srcSpan' name')
                           typeArgs'
                           args'
                           rhs'
                           maybeRetType'
              )
  return (decls', Map.fromList nameMap)

-- | Replaces the function names in the given 'ConstArg' using the given map.
renameConstArg :: Map HS.QName HS.QName -> ConstArg -> ConstArg
renameConstArg nameMap constArg = constArg
  { constArgIdents   = renameKeys (constArgIdents constArg)
  , constArgIndicies = renameKeys (constArgIndicies constArg)
  }
 where
  -- | Replaces the keys of the given map using 'nameMap'.
  renameKeys :: Map HS.QName v -> Map HS.QName v
  renameKeys = Map.mapKeys (fromJust . flip Map.lookup nameMap)

-------------------------------------------------------------------------------
-- Argument and return types                                                 --
-------------------------------------------------------------------------------

-- | Gets a map that maps the names of the arguments (qualified with the
--   function name) of the given function declaration to their annotated
--   type and a second map that maps the function names to their annotated
--   return types.
argAndReturnTypeMaps
  :: HS.FuncDecl
  -> Converter (Map (HS.QName, String) HS.Type, Map HS.QName HS.Type)
argAndReturnTypeMaps (HS.FuncDecl _ (HS.DeclIdent _ name) _ args _ maybeRetType)
  = return (argTypeMap, returnTypeMap)
 where
  argTypeMap = Map.fromList
    [ ((name, HS.varPatIdent arg), argType)
    | arg     <- args
    , argType <- maybeToList (HS.varPatType arg)
    ]
  returnTypeMap =
    Map.fromList [ (name, retType) | retType <- maybeToList maybeRetType ]

-- | Looks up the type of a constant argument in the given argument type
--   map (see 'argAndReturnTypeMaps').
--
--   Does not check whether all arguments have the same type but returns the
--   first matching type.
lookupConstArgType
  :: Map (HS.QName, String) HS.Type
  -> ConstArg
  -> Converter (HS.Type, Subst HS.Type)
lookupConstArgType argTypeMap constArg = do
  let idents  = Map.assocs (constArgIdents constArg)
      types   = catMaybes $ map (flip Map.lookup argTypeMap) idents
      srcSpan = HS.typeSrcSpan (head types)
  -- Unify all annotated types of the constant argument.
  -- TODO expansion and resolving should not be necessary anymore
  expandedTypes <- mapM expandAllTypeSynonyms types
  resolvedTypes <- mapM resolveTypes expandedTypes
  mgu           <- unifyAllOrFail srcSpan resolvedTypes
  constArgType  <- applySubst mgu (head resolvedTypes)
  return (constArgType, mgu)

-------------------------------------------------------------------------------
-- Generating @Variable@ sentences                                           --
-------------------------------------------------------------------------------

-- | Tests whether the given (renamed) function declaration uses the constant
--   argument.
isConstArgUsedBy :: ConstArg -> HS.FuncDecl -> Bool
isConstArgUsedBy constArg funcDecl =
  HS.UnQual (HS.Ident (constArgFreshIdent constArg))
    `Set.member` varSet (HS.funcDeclRhs funcDecl)

-- | Generates the @Variable@ sentence for the type variables in the given
--   types of the constant arguments.
generateConstTypeArgSentence
  :: [HS.TypeVarIdent] -> Converter (Maybe G.Sentence)
generateConstTypeArgSentence typeVarIdents
  | null typeVarIdents = return Nothing
  | otherwise = do
    let srcSpans = repeat NoSrcSpan
    typeVarIdents' <- zipWithM renameAndDefineTypeVar srcSpans typeVarIdents
    return (Just (G.variable typeVarIdents' G.sortType))

-- | Generates a @Variable@ sentence for a constant argument with the
--   given type.
generateConstArgVariable :: ConstArg -> HS.Type -> Converter G.Sentence
generateConstArgVariable constArg constArgType = do
  let ident = constArgFreshIdent constArg
  constArgType' <- convertType constArgType
  ident'        <- renameAndDefineVar NoSrcSpan False ident (Just constArgType)
  return (G.variable [ident'] constArgType')

-------------------------------------------------------------------------------
-- Removing constant arguments                                               --
-------------------------------------------------------------------------------

-- | Removes constant arguments from the argument list of the given
--   function declaration and replaces the argument by the fresh
--   identifier of the constant argument.
--
--   The constant arguments are also removed from calls to functions
--   that share the constant argument.
removeConstArgsFromFuncDecl
  :: [ConstArg] -> HS.FuncDecl -> Converter HS.FuncDecl
removeConstArgsFromFuncDecl constArgs (HS.FuncDecl srcSpan declIdent typeArgs args rhs maybeRetType)
  = do
    let name = HS.declIdentName declIdent
        removedArgs =
          fromJust
            $ Map.lookup name
            $ Map.unionsWith (++)
            $ map (Map.map return)
            $ map constArgIdents constArgs
        freshArgs = map constArgFreshIdent constArgs
        args' = [ arg | arg <- args, HS.varPatIdent arg `notElem` removedArgs ]
        subst = composeSubsts
          [ singleSubst' (HS.UnQual (HS.Ident removedArg))
                         (flip HS.untypedVar (HS.UnQual (HS.Ident freshArg)))
          | (removedArg, freshArg) <- zip removedArgs freshArgs
          ]
    rhs' <- applySubst subst rhs >>= removeConstArgsFromExpr constArgs
    return (HS.FuncDecl srcSpan declIdent typeArgs args' rhs' maybeRetType)

-- | Removes constant arguments from the applications in the given expressions.
removeConstArgsFromExpr :: [ConstArg] -> HS.Expr -> Converter HS.Expr
removeConstArgsFromExpr constArgs rootExpr = do
  (rootExpr', []) <- removeConstArgsFromExpr' rootExpr
  return rootExpr'
 where
  -- | Maps the name of functions that share the constant arguments to
  --   the indices of their corresponding argument.
  constArgIndicesMap :: Map HS.QName [Int]
  constArgIndicesMap =
    Map.unionsWith (++) $ map (Map.map return) $ map constArgIndicies constArgs

  -- | Looks up the indices of arguments that can be removed from the
  --   application of a function with the given name.
  lookupConstArgIndicies :: HS.QName -> Converter [Int]
  lookupConstArgIndicies name = do
    function <- inEnv $ isFunction name
    return (if function then lookupConstArgIndicies' name else [])

  -- | Like 'lookupConstArgIndicies' but assumes the function not to be
  --   shadowed by local varibales.
  lookupConstArgIndicies' :: HS.QName -> [Int]
  lookupConstArgIndicies' = fromMaybe [] . flip Map.lookup constArgIndicesMap

  -- | Implementation of 'removeConstArgsFromExpr' that returns the indices
  --   of the arguments that still need to be removed.
  removeConstArgsFromExpr'
    :: HS.Expr    -- ^ The expression to remove the constant arguments from.
    -> Converter (HS.Expr, [Int])

  -- If a variable is applied, lookup the indices of the arguments that
  -- can be removed.
  removeConstArgsFromExpr' expr@(HS.Var _ name _) = do
    indices <- lookupConstArgIndicies name
    return (expr, indices)

  -- Remove constant arguments from the applied expression. If the current
  -- argument (index @0@) needs to be removed, remove it. Otherwise remove
  -- constant arguments from the argument recursively.
  removeConstArgsFromExpr' (HS.App srcSpan e1 e2 exprType) = do
    (e1', indices) <- removeConstArgsFromExpr' e1
    let indices' = map (subtract 1) (filter (> 0) indices)
    if 0 `elem` indices
      then return (e1', indices')
      else do
        (e2', []) <- removeConstArgsFromExpr' e2
        return (HS.App srcSpan e1' e2' exprType, indices')

  -- Remove constant arguments recursively and pass through the indices of
  -- arguments that still have to be removed.
  removeConstArgsFromExpr' (HS.TypeAppExpr srcSpan expr typeExpr exprType) = do
    (expr', indices) <- removeConstArgsFromExpr' expr
    return (HS.TypeAppExpr srcSpan expr' typeExpr exprType, indices)

  -- Remove constant arguments recursively.
  removeConstArgsFromExpr' (HS.Lambda srcSpan varPats expr exprType) =
    shadowVarPats varPats $ do
      (expr', []) <- removeConstArgsFromExpr' expr
      return (HS.Lambda srcSpan varPats expr' exprType, [])
  removeConstArgsFromExpr' (HS.If srcSpan e1 e2 e3 exprType) = do
    (e1', []) <- removeConstArgsFromExpr' e1
    (e2', []) <- removeConstArgsFromExpr' e2
    (e3', []) <- removeConstArgsFromExpr' e3
    return (HS.If srcSpan e1' e2' e3' exprType, [])
  removeConstArgsFromExpr' (HS.Case srcSpan expr alts exprType) = do
    (expr', []) <- removeConstArgsFromExpr' expr
    alts'       <- mapM removeConstArgsFromAlt alts
    return (HS.Case srcSpan expr' alts' exprType, [])

  -- Leave all other expressions unchanged.
  removeConstArgsFromExpr' expr@(HS.Con _ _ _       ) = return (expr, [])
  removeConstArgsFromExpr' expr@(HS.Undefined _ _   ) = return (expr, [])
  removeConstArgsFromExpr' expr@(HS.ErrorExpr  _ _ _) = return (expr, [])
  removeConstArgsFromExpr' expr@(HS.IntLiteral _ _ _) = return (expr, [])

  -- | Applies 'removeConstArgsFromExpr'' to the right-hand side of the
  --   given @case@ expression alternative.
  removeConstArgsFromAlt :: HS.Alt -> Converter HS.Alt
  removeConstArgsFromAlt (HS.Alt srcSpan conPat varPats expr) =
    shadowVarPats varPats $ do
      (expr', []) <- removeConstArgsFromExpr' expr
      return (HS.Alt srcSpan conPat varPats expr')

-------------------------------------------------------------------------------
-- Updating the environment                                                  --
-------------------------------------------------------------------------------

-- | Modifies the type signature of the given function declaration, such that
--   it does not include the removed constant arguments anymore.
--
--   Returns the name of the function declaration and a list of type
--   argument indices that have been removed.
updateTypeSig
  :: Subst HS.Type
     -- ^ The most general unificator for the constant argument types.
  -> [HS.TypeVarIdent]
     -- ^ The type arguments declared in the section already.
  -> Map (HS.QName, String) HS.Type
     -- ^ The types of the arguments by function and argument name.
  -> Map HS.QName HS.Type
     -- ^ The return types by function name.
  -> HS.FuncDecl
    -- ^ The function declaration whose type signature to update.
  -> Converter (HS.QName, [Int])
updateTypeSig mgu constTypeVars argTypeMap returnTypeMap funcDecl = do
    -- TODO do we have to update type annotations in the AST?
    -- Lookup entry.
  let name = HS.funcDeclQName funcDecl
      args = HS.funcDeclArgs funcDecl
  Just entry <- inEnv $ lookupEntry ValueScope name
  -- Modify entry.
  -- Since the arguments of the @Free@ monad have been defined in the
  -- section already, 'entryNeedsFreeArgs' can be set to @False@.
  let argIdents = map HS.varPatIdent args
      funcArgs  = zip (repeat name) argIdents
  typeArgVars <- mapM (applySubst mgu . HS.TypeVar NoSrcSpan)
                      (entryTypeArgs entry)
  argTypes <- mapM (applySubst mgu)
                   (catMaybes (map (flip Map.lookup argTypeMap) funcArgs))
  returnType <- applySubst mgu (fromJust (Map.lookup name returnTypeMap))
  let allTypeArgs = map HS.typeVarIdent typeArgVars
      entry'      = entry { entryArity         = length args
                          , entryTypeArgs      = allTypeArgs \\ constTypeVars
                          , entryArgTypes      = map Just argTypes
                          , entryReturnType    = Just returnType
                          , entryNeedsFreeArgs = False
                          }
  modifyEnv $ addEntry entry'
  -- Update the index of the decreasing argument if it has been
  -- specified by the user.
  maybeDecArgIdent <- inEnv $ lookupDecArgIdent name
  case maybeDecArgIdent of
    Just decArgIdent -> do
      let Just decArgIndex = elemIndex decArgIdent argIdents
      modifyEnv $ defineDecArg name decArgIndex decArgIdent
    Nothing -> return ()
  -- Return the indices of removed type arguments.
  let removedTypeArgIndices =
        catMaybes $ map (`elemIndex` allTypeArgs) constTypeVars
  return (name, removedTypeArgIndices)

-------------------------------------------------------------------------------
-- Removing constant type arguments                                          --
-------------------------------------------------------------------------------

-- | Removes the type arguments that have been removed from the type
--   signature of function declarations from the type argument list of the
--   given function declaration and from visible type applications on its
--   right-hand side.
removeConstTypeArgsFromFuncDecl
  :: [(HS.QName, [Int])] -> HS.FuncDecl -> Converter HS.FuncDecl
removeConstTypeArgsFromFuncDecl constTypeVars funcDecl = do
  let rhs           = HS.funcDeclRhs funcDecl
      Just indices = lookup (HS.funcDeclQName funcDecl) constTypeVars
      typeArgs'     = removeIndicies indices (HS.funcDeclTypeArgs funcDecl)
  rhs' <- removeConstTypeArgsFromExpr constTypeVars rhs
  return funcDecl { HS.funcDeclTypeArgs = typeArgs', HS.funcDeclRhs = rhs' }

-- | Removes the elements with the given indices from the given list.
removeIndicies :: [Int] -> [a] -> [a]
removeIndicies _ [] = []
removeIndicies indices (x : xs) | 0 `elem` indices = xs'
                                 | otherwise         = x : xs'
 where
  indices' = map (subtract 1) (filter (> 0) indices)
  xs'       = removeIndicies indices' xs

-- | Removes the type arguments that have been removed from the type
--   signature of function declarations from visible type applications
--   in the given expression.
removeConstTypeArgsFromExpr
  :: [(HS.QName, [Int])] -> HS.Expr -> Converter HS.Expr
removeConstTypeArgsFromExpr constTypeVars rootExpr = do
  (rootExpr', []) <- removeConstTypeArgsFromExpr' rootExpr
  return rootExpr'
 where
  -- | Maps names of functions that share constant arguments to the indices
  --   of their constant type arguments.
  constTypeVarMap :: Map HS.QName [Int]
  constTypeVarMap = Map.fromList constTypeVars

  -- | Looks up the indices of the constant arguments that can be removed
  --   from a call to the function with the given name.
  lookupConstTypeArgIndicies :: HS.QName -> Converter [Int]
  lookupConstTypeArgIndicies name = do
    function <- inEnv $ isFunction name
    return (if function then lookupConstTypeArgIndicies' name else [])

  -- | Like 'lookupConstTypeArgIndicies' but assumes the function not to be
  --   shadowed by local varibales.
  lookupConstTypeArgIndicies' :: HS.QName -> [Int]
  lookupConstTypeArgIndicies' = fromMaybe [] . flip Map.lookup constTypeVarMap

  -- | Removes the type arguments recursively.
  removeConstTypeArgsFromExpr' :: HS.Expr -> Converter (HS.Expr, [Int])

  -- Lookup the indices of the type arguments that need to be removed.
  removeConstTypeArgsFromExpr' expr@(HS.Var _ varName _) = do
    indices <- lookupConstTypeArgIndicies varName
    return (expr, indices)

  -- Remove the current type argument (with index 0) or keep it.
  removeConstTypeArgsFromExpr' (HS.TypeAppExpr srcSpan expr typeExpr exprType)
    = do
      (expr', indices) <- removeConstTypeArgsFromExpr' expr
      let indices' = map (subtract 1) (filter (> 0) indices)
      if 0 `elem` indices
        then return (expr', indices')
        else return (HS.TypeAppExpr srcSpan expr' typeExpr exprType, indices')

  -- Remove constant type arguments recursively.
  removeConstTypeArgsFromExpr' (HS.App srcSpan e1 e2 exprType) = do
    (e1', []) <- removeConstTypeArgsFromExpr' e1
    (e2', []) <- removeConstTypeArgsFromExpr' e2
    return (HS.App srcSpan e1' e2' exprType, [])
  removeConstTypeArgsFromExpr' (HS.If srcSpan e1 e2 e3 exprType) = do
    (e1', []) <- removeConstTypeArgsFromExpr' e1
    (e2', []) <- removeConstTypeArgsFromExpr' e2
    (e3', []) <- removeConstTypeArgsFromExpr' e3
    return (HS.If srcSpan e1' e2' e3' exprType, [])
  removeConstTypeArgsFromExpr' (HS.Case srcSpan expr alts exprType) = do
    (expr', []) <- removeConstTypeArgsFromExpr' expr
    alts'       <- mapM removeConstTypeArgsFromAlt alts
    return (HS.Case srcSpan expr' alts' exprType, [])
  removeConstTypeArgsFromExpr' (HS.Lambda srcSpan args expr exprType) =
    shadowVarPats args $ do
      (expr', []) <- removeConstTypeArgsFromExpr' expr
      return (HS.Lambda srcSpan args expr' exprType, [])

  -- Leave all other nodes unchanged.
  removeConstTypeArgsFromExpr' expr@(HS.Con _ _ _       ) = return (expr, [])
  removeConstTypeArgsFromExpr' expr@(HS.Undefined _ _   ) = return (expr, [])
  removeConstTypeArgsFromExpr' expr@(HS.ErrorExpr  _ _ _) = return (expr, [])
  removeConstTypeArgsFromExpr' expr@(HS.IntLiteral _ _ _) = return (expr, [])

  -- | Applies 'removeConstTypeArgsFromExpr'' to the right-hand side of the
  --   given @case@ expression alternative.
  removeConstTypeArgsFromAlt :: HS.Alt -> Converter HS.Alt
  removeConstTypeArgsFromAlt (HS.Alt srcSpan conPat varPats expr) =
    shadowVarPats varPats $ do
      (expr', []) <- removeConstTypeArgsFromExpr' expr
      return (HS.Alt srcSpan conPat varPats expr')

-------------------------------------------------------------------------------
-- Interface functions                                                       --
-------------------------------------------------------------------------------

-- | Generates a @Definition@ sentence for the given function declaration
--   that passes the arguments to the function declared inside the @Section@
--   sentence in the correct order.
generateInterfaceDecl
  :: [ConstArg]
     -- ^ The constant arguments of the function.
  -> [Bool]
     -- ^ Whether the constant argument is used by any function.
  -> Map HS.QName HS.QName
     -- ^ Maps the names of the original functions to renamed/main functions.
  -> Subst HS.Type
     -- ^ The substitution of type variables of the function to type
     --   variables in the @Section@.
  -> [HS.TypeVarIdent]
     -- ^ The names of the @Section@'s type variables.
  -> [HS.TypeVarIdent]
     -- ^ The names of the renamed function's type variables.
  -> HS.FuncDecl
     -- ^ The original function declaration.
  -> Converter G.Sentence
generateInterfaceDecl constArgs isConstArgUsed nameMap mgu sectionTypeArgs renamedTypeArgs funcDecl
  = localEnv $ do
    let
      args          = HS.funcDeclArgs funcDecl
      name          = HS.funcDeclQName funcDecl
      constArgNames = map (HS.UnQual . HS.Ident) $ catMaybes $ map
        (Map.lookup name . constArgIdents)
        constArgs
      usedConstArgNames =
        map fst $ filter snd $ zip constArgNames isConstArgUsed

    -- The interface function is not recursive. Thus, we have to remove the
    -- decreasing argument, if one has been specified by the user.
    modifyEnv $ removeDecArg name

    -- Generate the left-hand side of the interface function definition.
    (qualid, binders, returnType') <- convertFuncHead funcDecl

    -- Lookup the name of the main function.
    let Just name' = Map.lookup name nameMap
    Just qualid' <- inEnv $ lookupIdent ValueScope name'

    -- Lookup the names of type arguments that have to be passed to the
    -- main function.
    let typeArgIdents = map HS.typeVarDeclIdent (HS.funcDeclTypeArgs funcDecl)
    typeArgNames <- mapM
      (lookupTypeArgName typeArgIdents (zip renamedTypeArgs [0 ..]))
      sectionTypeArgs
    typeArgNames' <-
      catMaybes <$> mapM (inEnv . lookupIdent TypeScope) typeArgNames

    -- Lookup the names of the constant arguments to pass to the main function.
    constArgNames' <-
      catMaybes <$> mapM (inEnv . lookupIdent ValueScope) usedConstArgNames

    -- If the function is partial, the @Partial@ instance needs to be passed
    -- to the main function.
    partialArg <- ifM (inEnv $ isPartial name)
                      (return [fst CoqBase.partialArg])
                      (return [])

    -- Lookup the names of all other arguments to pass to the main function.
    let nonConstArgNames = map HS.varPatQName args \\ constArgNames
    nonConstArgNames' <-
      catMaybes <$> mapM (inEnv . lookupIdent ValueScope) nonConstArgNames

    -- Generate invocation of the main function.
    -- TODO do we have to pass the remaining type arguments to the main
    --      function as well (using explicit type arguments)?
    let argNames' =
          typeArgNames' ++ constArgNames' ++ partialArg ++ nonConstArgNames'
        rhs' = genericApply qualid' [] [] (map G.Qualid argNames')
    return (G.definitionSentence qualid binders returnType' rhs')
 where
  -- | Looks up the name of the function's type argument that corresponds to
  --   the given type argument of the @Section@.
  lookupTypeArgName
    :: [HS.TypeVarIdent]
       -- ^ The type arguments of the function.
    -> [(HS.TypeVarIdent, Int)]
       -- ^ The renamed type arguments of the function and their index.
    -> HS.TypeVarIdent
       -- ^ The type argument of the section.
    -> Converter HS.QName
  lookupTypeArgName _ [] u =
    reportFatal
      $  Message (HS.funcDeclSrcSpan funcDecl) Error
      $  "Cannot find name of section type argument "
      ++ u
      ++ " for "
      ++ showPretty (HS.funcDeclQName funcDecl)
  lookupTypeArgName ws ((v, i) : vs) u = do
    (HS.TypeVar _ v') <- applySubst mgu (HS.TypeVar NoSrcSpan v)
    if v' == u
      then do
        let w = ws !! i
        return (HS.UnQual (HS.Ident w))
      else lookupTypeArgName ws vs u
