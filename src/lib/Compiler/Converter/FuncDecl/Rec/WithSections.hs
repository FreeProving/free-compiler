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
import           Data.Tuple.Extra               ( (&&&) )

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

-- | Converts recursive function decarations and adds a @Section@ sentence
--   for the given constant arguments.
convertRecFuncDeclsWithSection
  :: [ConstArg] -> [HS.FuncDecl] -> Converter [G.Sentence]
convertRecFuncDeclsWithSection constArgs decls = do
  -- Rename the function declarations in the section.
  (renamedDecls, identMap) <- renameFuncDecls decls
  let renamedConstArgs = map (renameConstArg identMap) constArgs
  renamedTypeArgs <- mapM
    ( fmap fromJust
    . inEnv
    . lookupTypeArgs ValueScope
    . HS.UnQual
    . HS.Ident
    . HS.fromDeclIdent
    . HS.getDeclIdent
    )
    renamedDecls

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

  -- Remove constant arguments from the renamed function declarations.
  sectionDecls <- mapM (removeConstArgsFromFuncDecl renamedConstArgs)
                       renamedDecls

  -- Remove the constant arguments from the type signature.

  -- Test which of the constant arguments is actually used by any function
  -- in the section and which of the type arguments is needed by the types
  -- of used .
  let isConstArgUsed = map (flip any sectionDecls . isConstArgUsedBy) constArgs
      usedConstArgTypes =
        map snd $ filter fst $ zip isConstArgUsed constArgTypes
      isTypeArgUsed v =
        any (Set.member (HS.UnQual (HS.Ident v)) . typeVarSet) usedConstArgTypes
      usedTypeArgIdents = filter isTypeArgUsed typeArgIdents

    -- Remove constant arguments from the type signatures of the renamed
    -- function declarations.
  mapM_ (updateTypeSig mgu usedTypeArgIdents argTypeMap returnTypeMap)
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
    let funcNames = map (HS.fromDeclIdent . HS.getDeclIdent) decls
    sectionIdent <- freshCoqIdent (intercalate "_" ("section" : funcNames))
    (helperDecls', mainDecls') <- sectionEnv
      $ convertRecFuncDeclsWithHelpers' sectionDecls
    return
      (G.SectionSentence
        (G.Section
          (G.ident sectionIdent)
          (  G.comment ("Constant arguments for " ++ intercalate ", " funcNames)
          :  genericArgVariables
          ++ maybeToList maybeTypeArgSentence
          ++ varSentences
          ++ G.comment ("Helper functions for " ++ intercalate ", " funcNames)
          :  helperDecls'
          ++ G.comment ("Main functions for " ++ intercalate ", " funcNames)
          :  mainDecls'
          )
        )
      )

  -- Add functions with correct argument order after the section.
  interfaceDecls' <- zipWithM
    (generateInterfaceDecl constArgs
                           isConstArgUsed
                           identMap
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
renameFuncDecls :: [HS.FuncDecl] -> Converter ([HS.FuncDecl], Map String String)
renameFuncDecls decls = do
  -- Create a substitution from old identifiers to fresh identifiers.
  modName <- inEnv envModName
  let idents = map (HS.fromDeclIdent . HS.getDeclIdent) decls
  idents' <- mapM freshHaskellIdent idents
  let identMap = zip idents idents'
      subst    = composeSubsts $ do
        (ident, ident') <- identMap
        name <- [HS.UnQual (HS.Ident ident), HS.Qual modName (HS.Ident ident)]
        let name' = HS.UnQual (HS.Ident ident')
        return (singleSubst' name (flip HS.Var name'))
  -- Rename function declarations, apply substituion to right-hand side
  -- and copy type signature and entry of original function.
  decls' <-
    flip mapM decls
      $ \(HS.FuncDecl srcSpan (HS.DeclIdent srcSpan' ident) args rhs) -> do
          let Just ident' = lookup ident identMap
              name        = HS.UnQual (HS.Ident ident)
              name'       = HS.UnQual (HS.Ident ident')
          -- Rename function references on right-hand side.
          rhs' <- applySubst subst rhs
          -- Lookup type signature and environment entry.
          (HS.TypeSchema _ typeArgDecls funcType) <- lookupTypeSigOrFail
            srcSpan'
            name
          entry <- lookupEntryOrFail srcSpan' ValueScope name
          -- Generate fresh identifiers for type variables.
          let typeArgs   = map HS.fromDeclIdent typeArgDecls
              argTypes   = entryArgTypes entry
              returnType = entryReturnType entry
          typeArgs' <- mapM freshHaskellIdent typeArgs
          let typeArgDecls' =
                zipWith (HS.DeclIdent . HS.getSrcSpan) typeArgDecls typeArgs'
              typeVarSubst = composeSubsts
                (zipWith singleSubst'
                         (map (HS.UnQual . HS.Ident) typeArgs)
                         (map (flip HS.TypeVar) typeArgs')
                )
          funcType'   <- applySubst typeVarSubst funcType
          argTypes'   <- mapM (mapM (applySubst typeVarSubst)) argTypes
          returnType' <- mapM (applySubst typeVarSubst) returnType

          -- Set type signature and environment entry for renamed function.
          let typeSchema' = HS.TypeSchema NoSrcSpan typeArgDecls' funcType'
          modifyEnv $ defineTypeSig name' typeSchema'
          _ <- renameAndAddEntry entry { entryName       = name'
                                       , entryTypeArgs   = typeArgs'
                                       , entryArgTypes   = argTypes'
                                       , entryReturnType = returnType'
                                       }

          -- If the decreasing argument of the original function has been
          -- annotated, copy that annotation.
          maybeDecArg <- inEnv $ lookupDecArg name
          case maybeDecArg of
            Just (decArgIndex, decArgIdent) ->
              modifyEnv $ defineDecArg name' decArgIndex decArgIdent
            Nothing -> return ()

          -- Rename function declaration.
          return (HS.FuncDecl srcSpan (HS.DeclIdent srcSpan' ident') args rhs')
  return (decls', Map.fromList identMap)

-- | Replaces the function names in the given 'ConstArg' using the given map.
renameConstArg :: Map String String -> ConstArg -> ConstArg
renameConstArg identMap constArg = constArg
  { constArgIdents   = renameKeys (constArgIdents constArg)
  , constArgIndicies = renameKeys (constArgIndicies constArg)
  }
 where
  -- | Replaces the keys of the given map using 'identMap'.
  renameKeys :: Map String v -> Map String v
  renameKeys = Map.mapKeys (fromJust . flip Map.lookup identMap)

-------------------------------------------------------------------------------
-- Argument and return types                                                 --
-------------------------------------------------------------------------------

-- | Gets a map that maps the names of the arguments (qualified with the
--   function name) of the given function declaration to their annotated
--   type and a second map that maps the function names to their annotated
--   return types.
argAndReturnTypeMaps
  :: HS.FuncDecl -> Converter (Map (String, String) HS.Type, Map String HS.Type)
argAndReturnTypeMaps (HS.FuncDecl srcSpan (HS.DeclIdent _ ident) args _) = do
  let name    = HS.UnQual (HS.Ident ident)
      funArgs = map (const ident &&& HS.fromVarPat) args
  (HS.TypeSchema _ _ funcType) <- lookupTypeSigOrFail srcSpan name
  (argTypes, returnType)       <- splitFuncType name args funcType
  return (Map.fromList (zip funArgs argTypes), Map.singleton ident returnType)

-- | Looks up the type of a constant argument in the given argument type
--   map (see 'argAndReturnTypeMaps').
--
--   Does not check whether all arguments have the same type but returns the
--   first matching type.
lookupConstArgType
  :: Map (String, String) HS.Type
  -> ConstArg
  -> Converter (HS.Type, Subst HS.Type)
lookupConstArgType argTypeMap constArg = do
  let idents = Map.assocs (constArgIdents constArg)
      types  = catMaybes $ map (flip Map.lookup argTypeMap) idents
  -- Unify all annotated types of the constant argument.
  expandedTypes <- mapM expandAllTypeSynonyms types
  resolvedTypes <- mapM resolveTypes expandedTypes
  mgu           <- unifyAll resolvedTypes
  constArgType  <- applySubst mgu (head resolvedTypes)
  return (constArgType, mgu)

-------------------------------------------------------------------------------
-- Generating @Variable@ sentences                                           --
-------------------------------------------------------------------------------

-- | Tests whether the given (renamed) function declaration uses the constant
--   argument.
isConstArgUsedBy :: ConstArg -> HS.FuncDecl -> Bool
isConstArgUsedBy constArg (HS.FuncDecl _ _ _ rhs) =
  HS.UnQual (HS.Ident (constArgFreshIdent constArg)) `Set.member` varSet rhs

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
  ident'        <- renameAndDefineVar NoSrcSpan False ident
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
removeConstArgsFromFuncDecl constArgs (HS.FuncDecl srcSpan declIdent args rhs)
  = do
    let ident = HS.fromDeclIdent declIdent
        removedArgs =
          fromJust
            $ Map.lookup ident
            $ Map.unionsWith (++)
            $ map (Map.map return)
            $ map constArgIdents constArgs
        freshArgs = map constArgFreshIdent constArgs
        args' = [ arg | arg <- args, HS.fromVarPat arg `notElem` removedArgs ]
        subst = composeSubsts
          [ singleSubst' (HS.UnQual (HS.Ident removedArg))
                         (flip HS.Var (HS.UnQual (HS.Ident freshArg)))
          | (removedArg, freshArg) <- zip removedArgs freshArgs
          ]
    rhs' <- applySubst subst rhs >>= removeConstArgsFromExpr constArgs
    return (HS.FuncDecl srcSpan declIdent args' rhs')

-- | Removes constant arguments from the applications in the given expressions.
removeConstArgsFromExpr :: [ConstArg] -> HS.Expr -> Converter HS.Expr
removeConstArgsFromExpr constArgs = flip removeConstArgsFromExpr' []
 where
  -- | Maps the name of functions that share the constant arguments to
  --   the indicies of their corresponding argument.
  constArgIndicesMap :: Map String [Int]
  constArgIndicesMap =
    Map.unionsWith (++) $ map (Map.map return) $ map constArgIndicies constArgs

  -- | Looks up the indicies of arguments that can be removed from the
  --   application of a function with the given name.
  lookupConstArgIndicies :: HS.QName -> Converter [Int]
  lookupConstArgIndicies (HS.UnQual name) =
    return (lookupConstArgIndicies' name)
  lookupConstArgIndicies (HS.Qual modName name) = do
    modName' <- inEnv envModName
    if modName == modName'
      then return []
      else return (lookupConstArgIndicies' name)

  -- | Like 'lookupConstArgIndicies' for unqualified names.
  lookupConstArgIndicies' :: HS.Name -> [Int]
  lookupConstArgIndicies' (HS.Ident ident) =
    fromMaybe [] $ Map.lookup ident constArgIndicesMap
  lookupConstArgIndicies' (HS.Symbol _) = []

  -- | Implementation of 'removeConstArgsFromExpr' that takes the current
  --   sub-expression as its first argument and the arguments it has been
  --   applied to as the second argument.
  removeConstArgsFromExpr'
    :: HS.Expr    -- ^ The expression to remove the constant arguments from.
    -> [HS.Expr]  -- ^ The arguments the expression is applied to.
    -> Converter HS.Expr

  -- If a variable is applied, lookup the indicies of the arguments that
  -- can be removed and remove them.
  removeConstArgsFromExpr' expr@(HS.Var _ name) args = do
    indicies <- lookupConstArgIndicies name
    let args' =
          map fst $ filter ((`notElem` indicies) . snd) $ zip args [0 ..]
    return (HS.app NoSrcSpan expr args')

  -- Remove the constant arguments from the argument and pass the argument
  -- to the applied expression such that it can remove it if necessary.
  removeConstArgsFromExpr' (HS.App _ e1 e2) args = do
    e2' <- removeConstArgsFromExpr' e2 []
    removeConstArgsFromExpr' e1 (e2' : args)

  -- Since we do not know in which branch there is a call to a function which
  -- shares the constant argument, we have to move the argument list into
  -- both branches and remove the arguments individually.
  removeConstArgsFromExpr' (HS.If srcSpan e1 e2 e3) args = do
    e1' <- removeConstArgsFromExpr' e1 []
    e2' <- removeConstArgsFromExpr' e2 args
    e3' <- removeConstArgsFromExpr' e3 args
    return (HS.If srcSpan e1' e2' e3')

  -- Similar to an @if@ expression, the arguments need to be moved into
  -- the alternatives of a @case@ expression.
  removeConstArgsFromExpr' (HS.Case srcSpan expr alts) args = do
    expr' <- removeConstArgsFromExpr' expr []
    alts' <- mapM (flip removeConstArgsFromAlt args) alts
    return (HS.Case srcSpan expr' alts')

  removeConstArgsFromExpr' (HS.Lambda srcSpan varPats expr) args =
    shadowVarPats varPats $ do
      expr' <- removeConstArgsFromExpr' expr args
      return (HS.Lambda srcSpan varPats expr')

  -- Leave all other expressions unchanged.
  removeConstArgsFromExpr' expr args = return (HS.app NoSrcSpan expr args)

  -- | Applies 'removeConstArgsFromExpr'' to the right-hand side of the
  --   given @case@ expression alternative.
  removeConstArgsFromAlt :: HS.Alt -> [HS.Expr] -> Converter HS.Alt
  removeConstArgsFromAlt (HS.Alt srcSpan conPat varPats expr) args =
    shadowVarPats varPats $ do
      expr' <- removeConstArgsFromExpr' expr args
      return (HS.Alt srcSpan conPat varPats expr')

-- | Modifies the type signature of the given function declaration, such that
--   it does not include the removed constant arguments anymore.
updateTypeSig
  :: Subst HS.Type
     -- ^ The most general unificator for the constant argument types.
  -> [HS.TypeVarIdent]
     -- ^ The type arguments declared in the section already.
  -> Map (String, String) HS.Type
     -- ^ The types of the arguments by function and argument name.
  -> Map String HS.Type
     -- ^ The return types by function name.
  -> HS.FuncDecl
    -- ^ The function declaration whose type signature to update.
  -> Converter ()
updateTypeSig mgu constTypeVars argTypeMap returnTypeMap (HS.FuncDecl _ declIdent args _)
  = do
    -- Lookup entry.
    let ident = HS.fromDeclIdent declIdent
        name  = HS.UnQual (HS.Ident ident)
    Just entry <- inEnv $ lookupEntry ValueScope name
  -- Modify type signature.
    let argIdents = map HS.fromVarPat args
        funArgs   = zip (repeat ident) argIdents
    typeArgVars <- mapM (applySubst mgu . HS.TypeVar NoSrcSpan)
                        (entryTypeArgs entry)
    argTypes <- mapM (applySubst mgu)
                     (catMaybes (map (flip Map.lookup argTypeMap) funArgs))
    returnType <- applySubst mgu (fromJust (Map.lookup ident returnTypeMap))
    let typeArgs =
          map (fromJust . HS.typeVarIdent) typeArgVars \\ constTypeVars
        typeArgsDecls = map (HS.DeclIdent NoSrcSpan) typeArgs
        funcType      = HS.funcType NoSrcSpan argTypes returnType
        typeSchema    = HS.TypeSchema NoSrcSpan typeArgsDecls funcType
    modifyEnv $ defineTypeSig name typeSchema
    -- Modify entry.
    -- Since the arguments of the @Free@ monad have been defined in the
    -- section already, 'entryNeedsFreeArgs' can be set to @False@.
    let entry' = entry { entryArity         = length args
                       , entryTypeArgs      = typeArgs
                       , entryArgTypes      = map Just argTypes
                       , entryReturnType    = Just returnType
                       , entryNeedsFreeArgs = False
                       }
    modifyEnv $ addEntry name entry'
    modifyEnv $ addEntry (entryName entry) entry'
    -- Update the index of the decreasing argument if it has been
    -- specified by the user.
    maybeDecArgIdent <- inEnv $ lookupDecArgIdent name
    case maybeDecArgIdent of
      Just decArgIdent -> do
        let Just decArgIndex = elemIndex decArgIdent argIdents
        modifyEnv $ defineDecArg name decArgIndex decArgIdent
      Nothing -> return ()

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
  -> Map String String
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
generateInterfaceDecl constArgs isConstArgUsed identMap mgu sectionTypeArgs renamedTypeArgs (HS.FuncDecl srcSpan (HS.DeclIdent _ ident) args _)
  = localEnv $ do
    let
      name          = HS.UnQual (HS.Ident ident)
      name'         = HS.UnQual (HS.Ident ident')
      Just ident'   = Map.lookup ident identMap
      constArgNames = map (HS.UnQual . HS.Ident) $ catMaybes $ map
        (Map.lookup ident . constArgIdents)
        constArgs
      usedConstArgNames =
        map fst $ filter snd $ zip constArgNames isConstArgUsed

    -- The interface function is not recursive. Thus, we have to remove the
    -- decreasing argument, if ne has been specified by the user
    modifyEnv $ removeDecArg name

    -- Generate the head of the interface function definition.
    (qualid, binders, returnType') <- convertFuncHead name args

    -- Lookup the name of the main function.
    Just qualid'                   <- inEnv $ lookupIdent ValueScope name'

    -- Lookup the names of type arguments that have to be passed to the
    -- main function.
    Just typeArgs                  <- inEnv $ lookupTypeArgs ValueScope name
    typeArgNames                   <- mapM
      (lookupTypeArgName typeArgs (zip renamedTypeArgs [0 ..]))
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
    let nonConstArgNames =
          map (HS.UnQual . HS.Ident . HS.fromVarPat) args \\ constArgNames
    nonConstArgNames' <-
      catMaybes <$> mapM (inEnv . lookupIdent ValueScope) nonConstArgNames

    -- Generate invocation of the main function.
    let argNames' =
          typeArgNames' ++ constArgNames' ++ partialArg ++ nonConstArgNames'
        rhs' = genericApply qualid' (map G.Qualid argNames')
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
      $  Message srcSpan Error
      $  "Cannot find name of section type argument "
      ++ u
      ++ " for "
      ++ ident
  lookupTypeArgName ws ((v, i) : vs) u = do
    (HS.TypeVar _ v') <- applySubst mgu (HS.TypeVar NoSrcSpan v)
    if v' == u
      then do
        let w = ws !! i
        return (HS.UnQual (HS.Ident w))
      else lookupTypeArgName ws vs u
