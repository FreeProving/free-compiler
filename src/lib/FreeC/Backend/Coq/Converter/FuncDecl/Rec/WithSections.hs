-- | This module contains functions for converting mutually recursive
--   functions with constant arguments by moving the constant arguments
--   into a @Section@ sentence.
--
--   A @Section@ sentence must be used in case of higher-order functions
--   to tell Coq that the function does not change. Otherwise Coq cannot
--   determine that functions using higher order functions terminate in
--   some cases.
module FreeC.Backend.Coq.Converter.FuncDecl.Rec.WithSections
  ( convertRecFuncDeclsWithSection
  ) where

import           Control.Monad
  ( forM, mapAndUnzipM, zipWithM )
import           Data.List
  ( (\\), elemIndex, intercalate )
import           Data.Map.Strict                                      ( Map )
import qualified Data.Map.Strict                                      as Map
import           Data.Maybe
  ( catMaybes, fromJust, fromMaybe, mapMaybe, maybeToList )
import qualified Data.Set                                             as Set

import           FreeC.Backend.Coq.Analysis.ConstantArguments
import qualified FreeC.Backend.Coq.Base                               as Coq.Base
import           FreeC.Backend.Coq.Converter.Free
import           FreeC.Backend.Coq.Converter.FuncDecl.Common
import           FreeC.Backend.Coq.Converter.FuncDecl.Rec.WithHelpers
import           FreeC.Backend.Coq.Converter.Type
import qualified FreeC.Backend.Coq.Syntax                             as Coq
import           FreeC.Environment
import           FreeC.Environment.Entry
import           FreeC.Environment.Fresh
import           FreeC.Environment.LookupOrFail
import           FreeC.Environment.Renamer
import           FreeC.IR.Reference
  ( freeTypeVarSet, freeVarSet )
import           FreeC.IR.SrcSpan
import           FreeC.IR.Subst
import qualified FreeC.IR.Syntax                                      as IR
import           FreeC.IR.Unification
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter
import           FreeC.Pretty

-- | Converts recursive function declarations and adds a @Section@ sentence
--   for the given constant arguments.
convertRecFuncDeclsWithSection
  :: [ConstArg] -> [IR.FuncDecl] -> Converter [Coq.Sentence]
convertRecFuncDeclsWithSection constArgs decls = do
  -- Rename the function declarations in the section.
  (renamedDecls, nameMap) <- renameFuncDecls decls
  let renamedConstArgs = map (renameConstArg nameMap) constArgs
      renamedTypeArgs  = map (map IR.typeVarDeclIdent . IR.funcDeclTypeArgs)
        renamedDecls
  -- Lookup the argument and return types of all function declarations.
  (argTypeMaps, returnTypeMaps)
    <- mapAndUnzipM argAndReturnTypeMaps renamedDecls
  let argTypeMap    = Map.unions argTypeMaps
      returnTypeMap = Map.unions returnTypeMaps
  -- Unify the argument and return types such that type variable names are
  -- unique.
  (constArgTypes, mgus) <- mapAndUnzipM (lookupConstArgType argTypeMap)
    renamedConstArgs
  let mgu           = composeSubsts mgus
      typeArgIdents = Set.toList (Set.unions (map freeTypeVarSet constArgTypes))
  -- Apply unifier to rename the type arguments on the right-hand side.
  let renamedDecls' = applySubst mgu renamedDecls
  -- Remove constant arguments from the renamed function declarations.
  sectionDecls <- mapM (removeConstArgsFromFuncDecl renamedConstArgs)
    renamedDecls'
  -- Test which of the constant arguments is actually used by any function
  -- in the section and which of the type arguments is needed by the types
  -- of used arguments.
  let isConstArgUsed    = map (flip any sectionDecls . isConstArgUsedBy)
        constArgs
      usedConstArgTypes
        = map snd $ filter fst $ zip isConstArgUsed constArgTypes
      isTypeArgUsed v = any (Set.member v . freeTypeVarSet) usedConstArgTypes
      usedTypeArgIdents = filter isTypeArgUsed typeArgIdents
    -- Remove constant arguments from the type signatures of the renamed
    -- function declarations.
  removedConstTypeArgs <- mapM
    (updateTypeSig mgu usedTypeArgIdents argTypeMap returnTypeMap) sectionDecls
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
    varSentences <- zipWithM generateConstArgVariable
      (map fst $ filter snd $ zip renamedConstArgs isConstArgUsed)
      (map fst $ filter snd $ zip constArgTypes isConstArgUsed)
    -- Generate a section identifier from the names of the original functions
    -- and convert the renamed functions as usual.
    let funcNames  = map IR.funcDeclQName decls
        funcIdents = mapMaybe IR.identFromQName funcNames
    sectionIdent <- freshCoqIdent (intercalate "_" ("section" : funcIdents))
    (helperDecls', mainDecls') <- convertRecFuncDeclsWithHelpers' sectionDecls'
    return
      (Coq.SectionSentence
       (Coq.Section (Coq.ident sectionIdent)
        (Coq.comment ("Constant arguments for " ++ intercalate ", " funcIdents)
         : genericArgVariables
         ++ maybeToList maybeTypeArgSentence
         ++ varSentences
         ++ Coq.comment ("Helper functions for " ++ intercalate ", " funcIdents)
         : helperDecls'
         ++ Coq.comment ("Main functions for " ++ intercalate ", " funcIdents)
         : mainDecls')))
  -- Add functions with correct argument order after the section.
  interfaceDecls'
    <- zipWithM (generateInterfaceDecl constArgs isConstArgUsed nameMap mgu
                 usedTypeArgIdents) renamedTypeArgs decls
  return (section : interfaceDecls')

-------------------------------------------------------------------------------
-- Renaming Functions, Arguments and Type Variables                          --
-------------------------------------------------------------------------------
-- | Renames the given function declarations using fresh identifiers.
--
--   The type signatures and environment entries are copied from the
--   original function.
--
--   Fresh identifiers are also generated for type variables in the type
--   signatures.
--
--   Returns the renamed function declarations and a map from old names
--   to new names.
renameFuncDecls
  :: [IR.FuncDecl] -> Converter ([IR.FuncDecl], Map IR.QName IR.QName)
renameFuncDecls decls = do
  -- Create a substitution from old identifiers to fresh identifiers.
  let names = map IR.funcDeclQName decls
  names' <- mapM freshHaskellQName names
  let nameMap = zip names names'
      subst   = composeSubsts $ do
        (name, name') <- nameMap
        return (singleSubst' name (flip IR.untypedVar name'))
  -- Rename function declarations, apply substituion to right-hand side
  -- and copy type signature and entry of original function.
  decls' <- forM decls
    $ \(IR.FuncDecl srcSpan (IR.DeclIdent srcSpan' name) typeArgs args
        maybeRetType rhs) -> do
      let Just name' = lookup name nameMap
      -- Generate fresh identifiers for type variables.
      let typeArgIdents = map IR.typeVarDeclIdent typeArgs
      typeArgIdents' <- mapM freshHaskellIdent typeArgIdents
      let typeArgs'     = zipWith IR.TypeVarDecl
            (map IR.typeVarDeclSrcSpan typeArgs) typeArgIdents'
          typeVarSubst  = composeSubsts
            (zipWith singleSubst' (map (IR.UnQual . IR.Ident) typeArgIdents)
             (map (flip IR.TypeVar) typeArgIdents'))
          args'         = applySubst typeVarSubst args
          maybeRetType' = applySubst typeVarSubst maybeRetType
      -- Set environment entry for renamed function.
      entry <- lookupEntryOrFail srcSpan' IR.ValueScope name
      _ <- renameAndAddEntry entry
        { entryName       = name'
        , entryTypeArgs   = typeArgIdents'
        , entryArgTypes   = map (fromJust . IR.varPatType) args'
        , entryReturnType = fromJust maybeRetType'
        }
      -- If the decreasing argument of the original function has been
      -- annotated, copy that annotation.
      maybeDecArg <- inEnv $ lookupDecArg name
      case maybeDecArg of
        Just (decArgIndex, decArgIdent) ->
          modifyEnv $ defineDecArg name' decArgIndex decArgIdent
        Nothing -> return ()
      -- Rename function references and type variables on right-hand side.
      let rhs' = applySubst typeVarSubst (applySubst subst rhs)
      -- Rename function declaration.
      return (IR.FuncDecl srcSpan (IR.DeclIdent srcSpan' name') typeArgs' args'
              maybeRetType' rhs')
  return (decls', Map.fromList nameMap)

-- | Replaces the function names in the given 'ConstArg' using the given map.
renameConstArg :: Map IR.QName IR.QName -> ConstArg -> ConstArg
renameConstArg nameMap constArg = constArg
  { constArgIdents   = renameKeys (constArgIdents constArg)
  , constArgIndicies = renameKeys (constArgIndicies constArg)
  }
 where
  -- | Replaces the keys of the given map using 'nameMap'.
  renameKeys :: Map IR.QName v -> Map IR.QName v
  renameKeys = Map.mapKeys (fromJust . flip Map.lookup nameMap)

-------------------------------------------------------------------------------
-- Argument and Return Types                                                 --
-------------------------------------------------------------------------------
-- | Gets a map that maps the names of the arguments (qualified with the
--   function name) of the given function declaration to their annotated
--   type and a second map that maps the function names to their annotated
--   return types.
argAndReturnTypeMaps
  :: IR.FuncDecl
  -> Converter (Map (IR.QName, String) IR.Type, Map IR.QName IR.Type)
argAndReturnTypeMaps (IR.FuncDecl _ (IR.DeclIdent _ name) _ args maybeRetType _)
  = return (argTypeMap, returnTypeMap)
 where
  argTypeMap    = Map.fromList
    [((name, IR.varPatIdent arg), argType)
    | arg <- args
    , argType <- maybeToList (IR.varPatType arg)
    ]

  returnTypeMap
    = Map.fromList [(name, retType) | retType <- maybeToList maybeRetType]

-- | Looks up the type of a constant argument in the given argument type
--   map (see 'argAndReturnTypeMaps').
--
--   Does not check whether all arguments have the same type but returns the
--   first matching type.
lookupConstArgType :: Map (IR.QName, String) IR.Type
                   -> ConstArg
                   -> Converter (IR.Type, Subst IR.Type)
lookupConstArgType argTypeMap constArg = do
  let idents  = Map.assocs (constArgIdents constArg)
      types   = mapMaybe (flip Map.lookup argTypeMap) idents
      srcSpan = IR.typeSrcSpan (head types)
  -- Unify all annotated types of the constant argument.
  mgu <- unifyAllOrFail srcSpan types
  let constArgType = applySubst mgu (head types)
  return (constArgType, mgu)

-------------------------------------------------------------------------------
-- Generating @Variable@ Sentences                                           --
-------------------------------------------------------------------------------
-- | Tests whether the given (renamed) function declaration uses the constant
--   argument.
isConstArgUsedBy :: ConstArg -> IR.FuncDecl -> Bool
isConstArgUsedBy constArg funcDecl = IR.UnQual
  (IR.Ident (constArgFreshIdent constArg))
  `Set.member` freeVarSet (IR.funcDeclRhs funcDecl)

-- | Generates the @Variable@ sentence for the type variables in the given
--   types of the constant arguments.
generateConstTypeArgSentence
  :: [IR.TypeVarIdent] -> Converter (Maybe Coq.Sentence)
generateConstTypeArgSentence typeVarIdents
  | null typeVarIdents = return Nothing
  | otherwise = do
    let srcSpans = repeat NoSrcSpan
    typeVarIdents' <- zipWithM renameAndDefineTypeVar srcSpans typeVarIdents
    return (Just (Coq.variable typeVarIdents' Coq.sortType))

-- | Generates a @Variable@ sentence for a constant argument with the
--   given type.
generateConstArgVariable :: ConstArg -> IR.Type -> Converter Coq.Sentence
generateConstArgVariable constArg constArgType = do
  let ident = constArgFreshIdent constArg
  constArgType' <- convertType constArgType
  ident' <- renameAndDefineVar NoSrcSpan False ident (Just constArgType)
  return (Coq.variable [ident'] constArgType')

-------------------------------------------------------------------------------
-- Removing Constant Arguments                                               --
-------------------------------------------------------------------------------
-- | Removes constant arguments from the argument list of the given
--   function declaration and replaces the argument by the fresh
--   identifier of the constant argument.
--
--   The constant arguments are also removed from calls to functions
--   that share the constant argument.
removeConstArgsFromFuncDecl
  :: [ConstArg] -> IR.FuncDecl -> Converter IR.FuncDecl
removeConstArgsFromFuncDecl constArgs
  (IR.FuncDecl srcSpan declIdent typeArgs args maybeRetType rhs) = do
    let name        = IR.declIdentName declIdent
        removedArgs = fromJust
          $ Map.lookup name
          $ Map.unionsWith (++)
          $ map (Map.map return . constArgIdents) constArgs
        freshArgs   = map constArgFreshIdent constArgs
        args'
          = [arg | arg <- args, IR.varPatIdent arg `notElem` removedArgs]
        subst       = composeSubsts
          [singleSubst' (IR.UnQual (IR.Ident removedArg))
            (flip IR.untypedVar (IR.UnQual (IR.Ident freshArg)))
          | (removedArg, freshArg) <- zip removedArgs freshArgs
          ]
    rhs' <- removeConstArgsFromExpr constArgs (applySubst subst rhs)
    return (IR.FuncDecl srcSpan declIdent typeArgs args' maybeRetType rhs')

-- | Removes constant arguments from the applications in the given expressions.
removeConstArgsFromExpr :: [ConstArg] -> IR.Expr -> Converter IR.Expr
removeConstArgsFromExpr constArgs rootExpr = do
  (rootExpr', []) <- removeConstArgsFromExpr' rootExpr
  return rootExpr'
 where
  -- | Maps the name of functions that share the constant arguments to
  --   the indices of their corresponding argument.
  constArgIndicesMap :: Map IR.QName [Int]
  constArgIndicesMap = Map.unionsWith (++)
    $ map (Map.map return . constArgIndicies) constArgs

  -- | Looks up the indices of arguments that can be removed from the
  --   application of a function with the given name.
  lookupConstArgIndicies :: IR.QName -> Converter [Int]
  lookupConstArgIndicies name = do
    function <- inEnv $ isFunction name
    return (if function then lookupConstArgIndicies' name else [])

  -- | Like 'lookupConstArgIndicies' but assumes the function not to be
  --   shadowed by local varibales.
  lookupConstArgIndicies' :: IR.QName -> [Int]
  lookupConstArgIndicies' = fromMaybe [] . flip Map.lookup constArgIndicesMap

  -- | Implementation of 'removeConstArgsFromExpr' that returns the indices
  --   of the arguments that still need to be removed.
  removeConstArgsFromExpr'
    :: IR.Expr -- ^ The expression to remove the constant arguments from.
    -> Converter (IR.Expr, [Int])

  -- If a variable is applied, lookup the indices of the arguments that
  -- can be removed.
  removeConstArgsFromExpr' expr@(IR.Var _ name _) = do
    indices <- lookupConstArgIndicies name
    return (expr, indices)
  -- Remove constant arguments from the applied expression. If the current
  -- argument (index @0@) needs to be removed, remove it. Otherwise remove
  -- constant arguments from the argument recursively.
  removeConstArgsFromExpr' (IR.App srcSpan e1 e2 exprType) = do
    (e1', indices) <- removeConstArgsFromExpr' e1
    let indices' = map (subtract 1) (filter (> 0) indices)
    if 0 `elem` indices then return (e1', indices') else do
      (e2', []) <- removeConstArgsFromExpr' e2
      return (IR.App srcSpan e1' e2' exprType, indices')
  -- Remove constant arguments recursively and pass through the indices of
  -- arguments that still have to be removed.
  removeConstArgsFromExpr' (IR.TypeAppExpr srcSpan expr typeExpr exprType) = do
    (expr', indices) <- removeConstArgsFromExpr' expr
    return (IR.TypeAppExpr srcSpan expr' typeExpr exprType, indices)
  -- Remove constant arguments recursively.
  removeConstArgsFromExpr' (IR.Lambda srcSpan varPats expr exprType)
    = shadowVarPats varPats $ do
      (expr', []) <- removeConstArgsFromExpr' expr
      return (IR.Lambda srcSpan varPats expr' exprType, [])
  removeConstArgsFromExpr' (IR.If srcSpan e1 e2 e3 exprType) = do
    (e1', []) <- removeConstArgsFromExpr' e1
    (e2', []) <- removeConstArgsFromExpr' e2
    (e3', []) <- removeConstArgsFromExpr' e3
    return (IR.If srcSpan e1' e2' e3' exprType, [])
  removeConstArgsFromExpr' (IR.Case srcSpan expr alts exprType) = do
    (expr', []) <- removeConstArgsFromExpr' expr
    alts' <- mapM removeConstArgsFromAlt alts
    return (IR.Case srcSpan expr' alts' exprType, [])
  removeConstArgsFromExpr' (IR.Let srcSpan binds expr exprType)
    = shadowVarPats (map IR.bindVarPat binds) $ do
      binds' <- mapM removeConstArgsFromBind binds
      (expr', []) <- removeConstArgsFromExpr' expr
      return (IR.Let srcSpan binds' expr' exprType, [])
  removeConstArgsFromExpr' (IR.Trace srcSpan msg expr exprType) = do
    (expr', []) <- removeConstArgsFromExpr' expr
    return (IR.Trace srcSpan msg expr' exprType, [])
  -- Leave all other expressions unchanged.
  removeConstArgsFromExpr' expr@(IR.Con _ _ _) = return (expr, [])
  removeConstArgsFromExpr' expr@(IR.Undefined _ _) = return (expr, [])
  removeConstArgsFromExpr' expr@(IR.ErrorExpr _ _ _) = return (expr, [])
  removeConstArgsFromExpr' expr@(IR.IntLiteral _ _ _) = return (expr, [])

  -- | Applies 'removeConstArgsFromExpr'' to the right-hand side of the
  --   given @case@ expression alternative.
  removeConstArgsFromAlt :: IR.Alt -> Converter IR.Alt
  removeConstArgsFromAlt (IR.Alt srcSpan conPat varPats expr)
    = shadowVarPats varPats $ do
      (expr', []) <- removeConstArgsFromExpr' expr
      return (IR.Alt srcSpan conPat varPats expr')

  -- | Applies 'removeConstArgsFromExpr'' to the right-hand side of the
  --   given @let@ binding.
  removeConstArgsFromBind :: IR.Bind -> Converter IR.Bind
  removeConstArgsFromBind (IR.Bind srcSpan varPat expr) = do
    (expr', []) <- removeConstArgsFromExpr' expr
    return (IR.Bind srcSpan varPat expr')

-------------------------------------------------------------------------------
-- Updating the Environment                                                  --
-------------------------------------------------------------------------------
-- | Modifies the type signature of the given function declaration, such that
--   it does not include the removed constant arguments anymore.
--
--   Returns the name of the function declaration and a list of type
--   argument indices that have been removed.
updateTypeSig
  :: Subst IR.Type
  -- ^ The most general unifier for the constant argument types.
  -> [IR.TypeVarIdent]
  -- ^ The type arguments declared in the section already.
  -> Map (IR.QName, String) IR.Type
  -- ^ The types of the arguments by function and argument name.
  -> Map IR.QName IR.Type
  -- ^ The return types by function name.
  -> IR.FuncDecl
  -- ^ The function declaration whose type signature to update.
  -> Converter (IR.QName, [Int])
updateTypeSig mgu constTypeVars argTypeMap returnTypeMap funcDecl = do
    -- TODO do we have to update type annotations in the AST?
    -- Lookup entry.
  let name = IR.funcDeclQName funcDecl
      args = IR.funcDeclArgs funcDecl
  Just entry <- inEnv $ lookupEntry IR.ValueScope name
  -- Modify entry.
  -- Since the arguments of the @Free@ monad have been defined in the
  -- section already, 'entryNeedsFreeArgs' can be set to @False@.
  let argIdents   = map IR.varPatIdent args
      funcArgs    = zip (repeat name) argIdents
      typeArgVars = applySubst mgu
        (map (IR.TypeVar NoSrcSpan) (entryTypeArgs entry))
      argTypes    = applySubst mgu (map (flip Map.lookup argTypeMap) funcArgs)
      returnType  = applySubst mgu (Map.lookup name returnTypeMap)
  let allTypeArgs = map IR.typeVarIdent typeArgVars
      entry'      = entry { entryArity         = length args
                          , entryTypeArgs      = allTypeArgs \\ constTypeVars
                          , entryArgTypes      = map fromJust argTypes
                          , entryReturnType    = fromJust returnType
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
    Nothing          -> return ()
  -- Return the indices of removed type arguments.
  let removedTypeArgIndices = mapMaybe (`elemIndex` allTypeArgs) constTypeVars
  return (name, removedTypeArgIndices)

-------------------------------------------------------------------------------
-- Removing Constant Type Arguments                                          --
-------------------------------------------------------------------------------
-- | Removes the type arguments that have been removed from the type
--   signature of function declarations from the type argument list of the
--   given function declaration and from visible type applications on its
--   right-hand side.
removeConstTypeArgsFromFuncDecl
  :: [(IR.QName, [Int])] -> IR.FuncDecl -> Converter IR.FuncDecl
removeConstTypeArgsFromFuncDecl constTypeVars funcDecl = do
  let rhs          = IR.funcDeclRhs funcDecl
      Just indices = lookup (IR.funcDeclQName funcDecl) constTypeVars
      typeArgs'    = removeIndicies indices (IR.funcDeclTypeArgs funcDecl)
  rhs' <- removeConstTypeArgsFromExpr constTypeVars rhs
  return funcDecl { IR.funcDeclTypeArgs = typeArgs', IR.funcDeclRhs = rhs' }

-- | Removes the elements with the given indices from the given list.
removeIndicies :: [Int] -> [a] -> [a]
removeIndicies _ [] = []
removeIndicies indices (x : xs) | 0 `elem` indices = xs'
                                | otherwise = x : xs'
 where
  indices' = map (subtract 1) (filter (> 0) indices)

  xs'      = removeIndicies indices' xs

-- | Removes the type arguments that have been removed from the type
--   signature of function declarations from visible type applications
--   in the given expression.
removeConstTypeArgsFromExpr
  :: [(IR.QName, [Int])] -> IR.Expr -> Converter IR.Expr
removeConstTypeArgsFromExpr constTypeVars rootExpr = do
  (rootExpr', []) <- removeConstTypeArgsFromExpr' rootExpr
  return rootExpr'
 where
  -- | Maps names of functions that share constant arguments to the indices
  --   of their constant type arguments.
  constTypeVarMap :: Map IR.QName [Int]
  constTypeVarMap = Map.fromList constTypeVars

  -- | Looks up the indices of the constant arguments that can be removed
  --   from a call to the function with the given name.
  lookupConstTypeArgIndicies :: IR.QName -> Converter [Int]
  lookupConstTypeArgIndicies name = do
    function <- inEnv $ isFunction name
    return (if function then lookupConstTypeArgIndicies' name else [])

  -- | Like 'lookupConstTypeArgIndicies' but assumes the function not to be
  --   shadowed by local variables.
  lookupConstTypeArgIndicies' :: IR.QName -> [Int]
  lookupConstTypeArgIndicies' = fromMaybe [] . flip Map.lookup constTypeVarMap

  -- | Removes the type arguments recursively.
  removeConstTypeArgsFromExpr' :: IR.Expr -> Converter (IR.Expr, [Int])

  -- Lookup the indices of the type arguments that need to be removed.
  removeConstTypeArgsFromExpr' expr@(IR.Var _ varName _) = do
    indices <- lookupConstTypeArgIndicies varName
    return (expr, indices)
  -- Remove the current type argument (with index 0) or keep it.
  removeConstTypeArgsFromExpr' (IR.TypeAppExpr srcSpan expr typeExpr exprType)
    = do
      (expr', indices) <- removeConstTypeArgsFromExpr' expr
      let indices' = map (subtract 1) (filter (> 0) indices)
      if 0 `elem` indices
        then return (expr', indices')
        else return (IR.TypeAppExpr srcSpan expr' typeExpr exprType, indices')
  -- Remove constant type arguments recursively.
  removeConstTypeArgsFromExpr' (IR.App srcSpan e1 e2 exprType) = do
    (e1', []) <- removeConstTypeArgsFromExpr' e1
    (e2', []) <- removeConstTypeArgsFromExpr' e2
    return (IR.App srcSpan e1' e2' exprType, [])
  removeConstTypeArgsFromExpr' (IR.If srcSpan e1 e2 e3 exprType) = do
    (e1', []) <- removeConstTypeArgsFromExpr' e1
    (e2', []) <- removeConstTypeArgsFromExpr' e2
    (e3', []) <- removeConstTypeArgsFromExpr' e3
    return (IR.If srcSpan e1' e2' e3' exprType, [])
  removeConstTypeArgsFromExpr' (IR.Case srcSpan expr alts exprType) = do
    (expr', []) <- removeConstTypeArgsFromExpr' expr
    alts' <- mapM removeConstTypeArgsFromAlt alts
    return (IR.Case srcSpan expr' alts' exprType, [])
  removeConstTypeArgsFromExpr' (IR.Lambda srcSpan args expr exprType)
    = shadowVarPats args $ do
      (expr', []) <- removeConstTypeArgsFromExpr' expr
      return (IR.Lambda srcSpan args expr' exprType, [])
  removeConstTypeArgsFromExpr' (IR.Let srcSpan binds expr exprType)
    = shadowVarPats (map IR.bindVarPat binds) $ do
      binds' <- mapM removeConstTypeArgsFromBind binds
      (expr', []) <- removeConstTypeArgsFromExpr' expr
      return (IR.Let srcSpan binds' expr' exprType, [])
  removeConstTypeArgsFromExpr' (IR.Trace srcSpan msg expr exprType) = do
    (expr', []) <- removeConstTypeArgsFromExpr' expr
    return (IR.Trace srcSpan msg expr' exprType, [])
  -- Leave all other nodes unchanged.
  removeConstTypeArgsFromExpr' expr@(IR.Con _ _ _) = return (expr, [])
  removeConstTypeArgsFromExpr' expr@(IR.Undefined _ _) = return (expr, [])
  removeConstTypeArgsFromExpr' expr@(IR.ErrorExpr _ _ _) = return (expr, [])
  removeConstTypeArgsFromExpr' expr@(IR.IntLiteral _ _ _) = return (expr, [])

  -- | Applies 'removeConstTypeArgsFromExpr'' to the right-hand side of the
  --   given @case@ expression alternative.
  removeConstTypeArgsFromAlt :: IR.Alt -> Converter IR.Alt
  removeConstTypeArgsFromAlt (IR.Alt srcSpan conPat varPats expr)
    = shadowVarPats varPats $ do
      (expr', []) <- removeConstTypeArgsFromExpr' expr
      return (IR.Alt srcSpan conPat varPats expr')

  -- | Applies 'removeConstTypeArgsFromExpr'' to the right-hand side of the
  --   given @let@ binding.
  removeConstTypeArgsFromBind :: IR.Bind -> Converter IR.Bind
  removeConstTypeArgsFromBind (IR.Bind srcSpan varPat expr) = do
    (expr', []) <- removeConstTypeArgsFromExpr' expr
    return (IR.Bind srcSpan varPat expr')

-------------------------------------------------------------------------------
-- Interface Functions                                                       --
-------------------------------------------------------------------------------
-- | Generates a @Definition@ sentence for the given function declaration
--   that passes the arguments to the function declared inside the @Section@
--   sentence in the correct order.
generateInterfaceDecl
  :: [ConstArg]
  -- ^ The constant arguments of the function.
  -> [Bool]
  -- ^ Whether the constant argument is used by any function.
  -> Map IR.QName IR.QName
  -- ^ Maps the names of the original functions to renamed/main functions.
  -> Subst IR.Type
  -- ^ The substitution of type variables of the function to type
  --   variables in the @Section@.
  -> [IR.TypeVarIdent]
  -- ^ The names of the @Section@'s type variables.
  -> [IR.TypeVarIdent]
  -- ^ The names of the renamed function's type variables.
  -> IR.FuncDecl
  -- ^ The original function declaration.
  -> Converter Coq.Sentence
generateInterfaceDecl constArgs isConstArgUsed nameMap mgu sectionTypeArgs
  renamedTypeArgs funcDecl = localEnv $ do
    let args              = IR.funcDeclArgs funcDecl
        name              = IR.funcDeclQName funcDecl
        constArgNames     = map (IR.UnQual . IR.Ident)
          $ mapMaybe (Map.lookup name . constArgIdents) constArgs
        usedConstArgNames
          = map fst $ filter snd $ zip constArgNames isConstArgUsed
    -- Generate the left-hand side of the interface function definition.
    (qualid, binders, returnType') <- convertFuncHead funcDecl
    -- Lookup the name of the main function.
    let Just name' = Map.lookup name nameMap
    Just qualid' <- inEnv $ lookupIdent IR.ValueScope name'
    -- Lookup the names of type arguments that have to be passed to the
    -- main function.
    let typeArgIdents = map IR.typeVarDeclIdent (IR.funcDeclTypeArgs funcDecl)
    typeArgNames <- mapM
      (lookupTypeArgName typeArgIdents (zip renamedTypeArgs [0 ..]))
      sectionTypeArgs
    typeArgNames' <- catMaybes
      <$> mapM (inEnv . lookupIdent IR.TypeScope) typeArgNames
    -- Lookup the names of the constant arguments to pass to the main function.
    constArgNames' <- catMaybes
      <$> mapM (inEnv . lookupIdent IR.ValueScope) usedConstArgNames
    -- Lookup the effects of the function and the instances that need to be
    -- passed to the main function.
    effects <- inEnv $ lookupEffects name
    let effectArgs       = concatMap Coq.Base.selectExplicitArgs effects
        -- Lookup the names of all other arguments to pass to the main function.
        nonConstArgNames = map IR.varPatQName args \\ constArgNames
    nonConstArgNames' <- catMaybes
      <$> mapM (inEnv . lookupIdent IR.ValueScope) nonConstArgNames
    -- Generate invocation of the main function.
    -- TODO do we have to pass the remaining type arguments to the main
    --      function as well (using explicit type arguments)?
    let argNames' = map Coq.Qualid (typeArgNames' ++ constArgNames')
          ++ effectArgs
          ++ map Coq.Qualid nonConstArgNames'
        rhs'      = genericApply qualid' [] [] argNames'
    return (Coq.definitionSentence qualid binders returnType' rhs')
 where
  -- | Looks up the name of the function's type argument that corresponds to
  --   the given type argument of the @Section@.
  lookupTypeArgName
    :: [IR.TypeVarIdent]
    -- ^ The type arguments of the function.
    -> [(IR.TypeVarIdent, Int)]
    -- ^ The renamed type arguments of the function and their index.
    -> IR.TypeVarIdent
    -- ^ The type argument of the section.
    -> Converter IR.QName
  lookupTypeArgName _ [] u             = reportFatal
    $ Message (IR.funcDeclSrcSpan funcDecl) Error
    $ "Cannot find name of section type argument "
    ++ u
    ++ " for "
    ++ showPretty (IR.funcDeclQName funcDecl)
  lookupTypeArgName ws ((v, i) : vs) u = do
    let IR.TypeVar _ v' = applySubst mgu (IR.TypeVar NoSrcSpan v)
    if v' == u then do
      let w = ws !! i
      return (IR.UnQual (IR.Ident w)) else lookupTypeArgName ws vs u
