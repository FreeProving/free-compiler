-- | This module contains functions for converting type synonym and data type
--   declarations and their constructors.
module FreeC.Backend.Coq.Converter.TypeDecl where

import Control.Monad ( mapAndUnzipM, foldM, replicateM )
import Control.Monad.Extra ( concatMapM )
import Data.List ( partition, nub )
import qualified Data.List.NonEmpty as NonEmpty
import Data.Maybe ( catMaybes, fromJust )
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified FreeC.Backend.Coq.Syntax as Coq
import FreeC.Backend.Coq.Converter.Arg
import FreeC.Backend.Coq.Converter.Free
import FreeC.Backend.Coq.Converter.Type
import qualified FreeC.Backend.Coq.Base as Coq.Base
import FreeC.Environment
import FreeC.Environment.Entry
import FreeC.Environment.LookupOrFail
import FreeC.Environment.Fresh
import FreeC.IR.DependencyGraph
import FreeC.IR.Subst
import qualified FreeC.IR.Syntax as IR
import FreeC.IR.TypeSynExpansion
import FreeC.IR.Unification
import FreeC.Monad.Converter
import FreeC.Monad.Reporter
import FreeC.Pretty
import FreeC.IR.SrcSpan ( SrcSpan(NoSrcSpan) )

-------------------------------------------------------------------------------
-- Strongly connected components                                             --
-------------------------------------------------------------------------------
-- | Converts a strongly connected component of the type dependency graph.
convertTypeComponent
    :: DependencyComponent IR.TypeDecl -> Converter [ Coq.Sentence ]
convertTypeComponent (NonRecursive decl)
    | isTypeSynDecl decl = convertTypeSynDecl decl
    | otherwise = convertDataDecls [ decl ]
convertTypeComponent (Recursive decls) = do
    let ( typeSynDecls, dataDecls ) = partition isTypeSynDecl decls
        typeSynDeclQNames = Set.fromList (map IR.typeDeclQName typeSynDecls)
    sortedTypeSynDecls <- sortTypeSynDecls typeSynDecls
    expandedDataDecls <- mapM
        (expandAllTypeSynonymsInDeclWhere (`Set.member` typeSynDeclQNames))
        dataDecls
    dataDecls' <- convertDataDecls expandedDataDecls
    typeSynDecls' <- concatMapM convertTypeSynDecl sortedTypeSynDecls
    return (dataDecls' ++ typeSynDecls')

-- | Sorts type synonym declarations topologically.
--
--   After filtering type synonym declarations from the a strongly connected
--   component, they are not mutually dependent on each other anymore (expect
--   if they form a cycle). However, type synonyms may still depend on other
--   type synonyms from the same strongly connected component. Therefore we
--   have to sort the declarations in reverse topological order.
sortTypeSynDecls :: [ IR.TypeDecl ] -> Converter [ IR.TypeDecl ]
sortTypeSynDecls = mapM fromNonRecursive . groupTypeDecls

-- | Extracts the single type synonym declaration from a strongly connected
--   component of the type dependency graph.
--
--   Reports a fatal error if the component contains mutually recursive
--   declarations (i.e. type synonyms form a cycle).
fromNonRecursive :: DependencyComponent IR.TypeDecl -> Converter IR.TypeDecl
fromNonRecursive (NonRecursive decl) = return decl
fromNonRecursive (Recursive decls) = reportFatal $ Message
    (IR.typeDeclSrcSpan (head decls)) Error
    $ "Type synonym declarations form a cycle: " ++ showPretty
    (map IR.typeDeclIdent decls)

-------------------------------------------------------------------------------
-- Type synonym declarations                                                 --
-------------------------------------------------------------------------------
-- | Tests whether the given declaration is a type synonym declaration.
isTypeSynDecl :: IR.TypeDecl -> Bool
isTypeSynDecl (IR.TypeSynDecl _ _ _ _) = True
isTypeSynDecl (IR.DataDecl _ _ _ _) = False

-- | Converts a Haskell type synonym declaration to Coq.
convertTypeSynDecl :: IR.TypeDecl -> Converter [ Coq.Sentence ]
convertTypeSynDecl decl@(IR.TypeSynDecl _ _ typeVarDecls typeExpr)
    = localEnv $ do
        let name = IR.typeDeclQName decl
        Just qualid <- inEnv $ lookupIdent IR.TypeScope name
        typeVarDecls' <- convertTypeVarDecls Coq.Explicit typeVarDecls
        typeExpr' <- convertType' typeExpr
        return [ Coq.definitionSentence qualid
                     (genericArgDecls Coq.Explicit ++ typeVarDecls')
                     (Just Coq.sortType) typeExpr'
               ]
-- Data type declarations are not allowed in this function.
convertTypeSynDecl (IR.DataDecl _ _ _ _)
    = error "convertTypeSynDecl: Data type declaration not allowed."

-------------------------------------------------------------------------------
-- Data type declarations                                                    --
-------------------------------------------------------------------------------
-- | Converts multiple (mutually recursive) Haskell data type declaration
--   declarations.
--
--   Before the declarations are actually translated, their identifiers are
--   inserted into the current environment. Otherwise the data types would
--   not be able to depend on each other. The identifiers for the constructors
--   are inserted into the current environment as well. This makes the
--   constructors more likely to keep their original name if there is a type
--   variable with the same (lowercase) name.
--
--   After the @Inductive@ sentences for the data type declarations there
--   is one @Arguments@ sentence and one smart constructor declaration for
--   each constructor declaration of the given data types.
convertDataDecls :: [ IR.TypeDecl ] -> Converter [ Coq.Sentence ]
convertDataDecls dataDecls = do
    ( indBodies, extraSentences ) <- mapAndUnzipM convertDataDecl dataDecls
    instances <- generateInstances dataDecls
    return
        (Coq.comment ("Data type declarations for " ++ showPretty
                      (map IR.typeDeclName dataDecls)) : Coq.InductiveSentence
         (Coq.Inductive (NonEmpty.fromList indBodies) [])
         : concat extraSentences ++ instances)

-- | Converts a Haskell data type declaration to the body of a Coq @Inductive@
--   sentence, the @Arguments@ sentences for it's constructors and the smart
--   constructor declarations.
--
--   Type variables declared by the data type or the smart constructors are
--   not visible outside of this function.
convertDataDecl :: IR.TypeDecl -> Converter ( Coq.IndBody, [ Coq.Sentence ] )
convertDataDecl (IR.DataDecl _ (IR.DeclIdent _ name) typeVarDecls conDecls) = do
    ( body, argumentsSentences ) <- generateBodyAndArguments
    smartConDecls <- mapM generateSmartConDecl conDecls
    return ( body
           , Coq.comment ("Arguments sentences for " ++ showPretty
                          (IR.toUnQual name)) : argumentsSentences
                 ++ Coq.comment ("Smart constructors for " ++ showPretty
                                 (IR.toUnQual name)) : smartConDecls
           )
  where
    -- | Generates the body of the @Inductive@ sentence and the @Arguments@
    --   sentences for the constructors but not the smart constructors
    --   of the data type.
    --
    --   Type variables declared by the data type declaration are visible to the
    --   constructor declarations and @Arguments@ sentences created by this
    --   function, but not outside this function. This allows the smart
    --   constructors to reuse the identifiers for their type arguments (see
    --   'generateSmartConDecl').
    generateBodyAndArguments :: Converter ( Coq.IndBody, [ Coq.Sentence ] )
    generateBodyAndArguments = localEnv $ do
        Just qualid <- inEnv $ lookupIdent IR.TypeScope name
        typeVarDecls' <- convertTypeVarDecls Coq.Explicit typeVarDecls
        conDecls' <- mapM convertConDecl conDecls
        argumentsSentences <- mapM generateArgumentsSentence conDecls
        return
            ( Coq.IndBody qualid (genericArgDecls Coq.Explicit ++ typeVarDecls')
                  Coq.sortType conDecls'
            , argumentsSentences
            )

    -- | Converts a constructor of the data type.
    convertConDecl :: IR.ConDecl
        -> Converter ( Coq.Qualid, [ Coq.Binder ], Maybe Coq.Term )
    convertConDecl (IR.ConDecl _ (IR.DeclIdent _ conName) args) = do
        Just conQualid <- inEnv $ lookupIdent IR.ValueScope conName
        Just returnType <- inEnv $ lookupReturnType IR.ValueScope conName
        args' <- mapM convertType args
        returnType' <- convertType' returnType
        return ( conQualid, [], Just (args' `Coq.arrows` returnType') )

    -- | Generates the @Arguments@ sentence for the given constructor declaration.
    generateArgumentsSentence :: IR.ConDecl -> Converter Coq.Sentence
    generateArgumentsSentence (IR.ConDecl _ (IR.DeclIdent _ conName) _) = do
        Just qualid <- inEnv $ lookupIdent IR.ValueScope conName
        let typeVarNames = map IR.typeVarDeclQName typeVarDecls
        typeVarQualids <- mapM (inEnv . lookupIdent IR.TypeScope) typeVarNames
        return (Coq.ArgumentsSentence
                (Coq.Arguments Nothing qualid
                 [ Coq.ArgumentSpec Coq.ArgMaximal (Coq.Ident typeVarQualid)
                     Nothing | typeVarQualid
                 <- map fst Coq.Base.freeArgs ++ catMaybes typeVarQualids
                 ]))

    -- | Generates the smart constructor declaration for the given constructor
    --   declaration.
    generateSmartConDecl :: IR.ConDecl -> Converter Coq.Sentence
    generateSmartConDecl (IR.ConDecl _ declIdent argTypes) = localEnv $ do
        let conName = IR.declIdentName declIdent
        Just qualid <- inEnv $ lookupIdent IR.ValueScope conName
        Just smartQualid <- inEnv $ lookupSmartIdent conName
        Just returnType <- inEnv $ lookupReturnType IR.ValueScope conName
        typeVarDecls' <- convertTypeVarDecls Coq.Implicit typeVarDecls
        ( argIdents', argDecls' ) <- mapAndUnzipM convertAnonymousArg
            (map Just argTypes)
        returnType' <- convertType returnType
        rhs <- generatePure
            (Coq.app (Coq.Qualid qualid) (map Coq.Qualid argIdents'))
        return (Coq.definitionSentence smartQualid
                (genericArgDecls Coq.Explicit ++ typeVarDecls' ++ argDecls')
                (Just returnType') rhs)
-- Type synonyms are not allowed in this function.
convertDataDecl (IR.TypeSynDecl _ _ _ _)
    = error "convertDataDecl: Type synonym not allowed."

------ Instance generation -------
generateInstances :: [ IR.TypeDecl ] -> Converter [ Coq.Sentence ]
generateInstances dataDecls = do
    nfInstances <- generateNormalformInstances
    return nfInstances
  where
    declTypes = map dataDeclToType dataDecls

    conNames = map IR.typeDeclQName dataDecls

    generateNormalformInstances :: Converter [ Coq.Sentence ]
    generateNormalformInstances = do
        topLevelMap <- nameFunctionsAndInsert "nf'" emptyTypeMap declTypes
        topLevelVars <- map Coq.bare <$> mapM freshCoqIdent
            (replicate (length declTypes) "x")
        nf' <- generateNf' topLevelMap dataDecls declTypes topLevelVars
        instances <- mapM (buildInstance topLevelMap) declTypes
        return (nf' : instances)

    buildInstance :: TypeMap -> IR.Type -> Converter Coq.Sentence
    buildInstance m t = localEnv $ do
        -- @nf' := nf'T@
        let instanceBody
                = ( Coq.bare "nf'", Coq.Qualid (fromJust (lookupType t m)) )
        -- Get the binders and return type for the instance declaration
        ( binders, retType ) <- makeNFInstanceBindersAndReturnType t
        instanceName <- Coq.bare <$> nameFunction "Normalform" t
        return $ Coq.InstanceSentence (Coq.InstanceDefinition instanceName
                                       binders retType [ instanceBody ] Nothing)

    generateNf' :: TypeMap -> [ IR.TypeDecl ]
        -> [ IR.Type ] -> [ Coq.Qualid ] -> Converter Coq.Sentence
    generateNf' topLevelMap dataDecls declTypes topLevelVars = localEnv $ do
        fixBodies <- mapM (uncurry (uncurry (makeFixBody topLevelMap)))
            (zip (zip topLevelVars declTypes) dataDecls)
        return $ Coq.FixpointSentence
            (Coq.Fixpoint (NonEmpty.fromList fixBodies) [])
      where
        makeFixBody :: TypeMap
            -> Coq.Qualid -> IR.Type -> IR.TypeDecl -> Converter Coq.FixBody
        makeFixBody m var t decl = do
            rhs <- generateBody m var decl t
            ( binders, retType ) <- makeNFBindersAndReturnType' t var
            return $ Coq.FixBody (fromJust (lookupType t m))
                (NonEmpty.fromList binders) Nothing (Just retType) rhs

        generateBody
            :: TypeMap -> Coq.Qualid -> IR.TypeDecl -> IR.Type -> Converter
            Coq.Term -- TODO: don't do that. Sort these functions properly.

        generateBody topLevelMap ident tDecl t = do
            let ts = nub (reverse (concatMap (collectSubTypes conNames)
                                   (concatMap IR.conDeclFields
                                    (IR.dataDeclCons tDecl))))
            let recTypes = filter
                    (\t -> not (t `elem` declTypes || isTypeVar t)) ts
            let typeVars = map (Coq.bare . IR.typeVarDeclIdent)
                    (IR.typeDeclArgs tDecl)
            targetVars <- (map Coq.bare) <$> replicateM (length typeVars)
                (freshCoqIdent "b")
            let freeQualids = map fst Coq.Base.freeArgs
            normalformFuncMap
                <- nameFunctionsAndInsert "nf'" topLevelMap recTypes
            nf'Body <- generateNf'Body normalformFuncMap ident t recTypes
            return nf'Body

        -- letfix distinction
        generateNf'Body :: TypeMap
            -> Coq.Qualid -> IR.Type -> [ IR.Type ] -> Converter Coq.Term
        generateNf'Body m ident t [] = matchConstructors m ident t
        generateNf'Body m ident t (recType : recTypes) = do
            inBody <- generateNf'Body m ident t recTypes
            var <- Coq.bare <$> freshCoqIdent "x"
            letBody <- matchConstructors m var recType
            ( binders, retType ) <- makeNFBindersAndReturnType' recType var
            let Just localFuncName = lookupType recType m
            return $ Coq.Let localFuncName [] Nothing
                (Coq.Fix (Coq.FixOne
                          (Coq.FixBody localFuncName (NonEmpty.fromList binders)
                           Nothing (Just retType) letBody))) inBody

        matchConstructors
            :: TypeMap -> Coq.Qualid -> IR.Type -> Converter Coq.Term
        matchConstructors m ident t = do
            let Just conName = getTypeConName t
            entry <- lookupEntryOrFail NoSrcSpan IR.TypeScope conName
            equations <- mapM (buildEquation m t) (entryConsNames entry)
            return $ Coq.match (Coq.Qualid ident) equations

        -- type: type expression for unification
        -- consName : data constructor name of type
        buildEquation :: TypeMap -> IR.Type -> IR.ConName -> Converter
            Coq.Equation -- TODO: rename type args before unification

        buildEquation m t conName = do
            conEntry <- lookupEntryOrFail NoSrcSpan IR.ValueScope conName
            let retType = entryReturnType conEntry
            let conIdent = entryIdent conEntry -- :: Qualid
            conArgIdents <- (map Coq.bare) <$> replicateM (entryArity conEntry)
                (freshCoqIdent "fx")
            subst <- unifyOrFail NoSrcSpan t retType
            let modArgTypes = map ((stripType conNames) . (applySubst subst))
                    (entryArgTypes conEntry)
            let lhs = Coq.ArgsPat conIdent (map Coq.QualidPat conArgIdents)
            rhs <- buildNormalformValue m conIdent []
                (zip modArgTypes conArgIdents)
            return $ Coq.equation lhs rhs

        -- TODO: Split into normal function and helper function because of the accumulator.
        buildNormalformValue :: TypeMap -> Coq.Qualid -> [ Coq.Qualid ]
            -> [ ( IR.Type, Coq.Qualid ) ] -> Converter Coq.Term
        buildNormalformValue nameMap consName vals [] = return $ applyPure
            (Coq.app (Coq.Qualid consName)
             (map (applyPure . Coq.Qualid) (reverse vals)))
        buildNormalformValue nameMap consName vals (( t, varName ) : consVars)
            = case lookupType t nameMap of
                Just funcName -> do
                    x <- Coq.bare <$> freshCoqIdent "x"
                    nx <- Coq.bare <$> freshCoqIdent "nx"
                    rhs <- buildNormalformValue nameMap consName (nx : vals)
                        consVars
                    let c = Coq.fun [ nx ] [ Nothing ] rhs
                    let c'' = applyBind (Coq.app (Coq.Qualid funcName)
                                         [ (Coq.Qualid x) ]) c
                    return $ applyBind (Coq.Qualid varName)
                        (Coq.fun [ x ] [ Nothing ] c'')
                Nothing -> do
                    nx <- Coq.bare <$> freshCoqIdent "nx"
                    rhs <- buildNormalformValue nameMap consName (nx : vals)
                        consVars
                    let cont = Coq.fun [ nx ] [ Nothing ] rhs
                    return $ applyBind (Coq.app (Coq.Qualid (Coq.bare "nf"))
                                        [ (Coq.Qualid varName) ]) cont

showPrettyType :: IR.Type -> Converter String
showPrettyType (IR.TypeVar _ varName) = return (showPretty varName)
showPrettyType (IR.TypeCon srcSpan conName) = do
    entry <- lookupEntryOrFail srcSpan IR.TypeScope conName
    let Just coqIdent = Coq.unpackQualid (entryIdent entry)
    return coqIdent
showPrettyType (IR.TypeApp _ l r) = do
    lPretty <- showPrettyType l
    rPretty <- showPrettyType r
    return (lPretty ++ rPretty)

collectSubTypes :: [ IR.ConName ] -> IR.Type -> [ IR.Type ]
collectSubTypes = collectFullyAppliedTypes True

collectFullyAppliedTypes :: Bool -> [ IR.ConName ] -> IR.Type -> [ IR.Type ]
collectFullyAppliedTypes fullApplication conNames t@(IR.TypeApp _ l r)
    | fullApplication = stripType conNames t : collectFullyAppliedTypes False
        conNames l ++ collectFullyAppliedTypes True conNames r
    | otherwise = collectFullyAppliedTypes False conNames l
        ++ collectFullyAppliedTypes True conNames r
collectFullyAppliedTypes _ conNames t = []

-- returns the same type with all 'don't care' types replaced by the variable "_"
stripType cs t = stripType' t cs False

stripType' :: IR.Type -> [ IR.ConName ] -> Bool -> IR.Type
stripType' (IR.TypeVar _ _) names flag = IR.TypeVar NoSrcSpan "_"
stripType' (IR.TypeCon _ conName) names flag
    | flag || conName `elem` names = IR.TypeCon NoSrcSpan conName
    | otherwise = IR.TypeVar NoSrcSpan "_"
stripType' (IR.TypeApp _ l r) names flag = case stripType' r names False of
    r'@(IR.TypeVar _ _) -> IR.TypeApp NoSrcSpan (stripType' l names flag) r'
    r' -> IR.TypeApp NoSrcSpan (stripType' l names True) r'

nameFunctionsAndInsert :: String -> TypeMap -> [ IR.Type ] -> Converter TypeMap
nameFunctionsAndInsert prefix m ts = localEnv $ foldM
    (nameFunctionAndInsert prefix) m ts

nameFunctionAndInsert :: String -> TypeMap -> IR.Type -> Converter TypeMap
nameFunctionAndInsert prefix m t = do
    name <- nameFunction prefix t
    return (insertType t (Coq.bare name) m)

-- Names a function based on a type while avoiding name clashes with other
-- identifiers.
nameFunction :: String -> IR.Type -> Converter String
nameFunction prefix t = do
    prettyType <- showPrettyType t
    freshCoqIdent (prefix ++ prettyType)

dataDeclToType :: IR.TypeDecl -> IR.Type
dataDeclToType dataDecl = IR.typeConApp NoSrcSpan (IR.typeDeclQName dataDecl)
    (replicate (length (IR.typeDeclArgs dataDecl)) (IR.TypeVar NoSrcSpan "_"))

isTypeVar :: IR.Type -> Bool
isTypeVar (IR.TypeVar _ _) = True
isTypeVar _ = False

-- duplicate of CompletePatternPass
getTypeConName :: IR.Type -> Maybe IR.ConName
getTypeConName (IR.TypeCon _ conName) = Just conName
getTypeConName (IR.TypeApp _ l r) = getTypeConName l
getTypeConName _ = Nothing

buildConstraint :: String -> [ Coq.Qualid ] -> Coq.Binder
buildConstraint ident args = Coq.Generalized Coq.Implicit
    (Coq.app (Coq.Qualid (Coq.bare ident))
     ((map (Coq.Qualid . fst) Coq.Base.freeArgs) ++ (map Coq.Qualid args)))

-- Coq AST helper functions 
freeArgsBinders :: [ Coq.Binder ]
freeArgsBinders = map (uncurry (Coq.typedBinder' Coq.Implicit))
    Coq.Base.freeArgs

typeBinder :: [ Coq.Qualid ] -> Coq.Binder
typeBinder typeVars = Coq.typedBinder Coq.Implicit typeVars Coq.sortType

-- TODO: Does this exist somewhere?
applyPure :: Coq.Term -> Coq.Term
applyPure t = Coq.app (Coq.Qualid Coq.Base.freePureCon) [ t ]

applyBind :: Coq.Term -> Coq.Term -> Coq.Term
applyBind mx f = Coq.app (Coq.Qualid Coq.Base.freeBind) [ mx, f ]

-- Given an A, returns Free Shape Pos A
applyFree :: Coq.Term -> Coq.Term
applyFree a = Coq.app (Coq.Qualid Coq.Base.free)
    ((map (Coq.Qualid . fst) Coq.Base.freeArgs) ++ [ a ])
    
shapeAndPos :: [ Coq.Term ]
shapeAndPos = map (Coq.Qualid . fst) Coq.Base.freeArgs

idShapeAndPos :: [ Coq.Term ]
idShapeAndPos
    = (map (Coq.Qualid . Coq.bare) [ "Identity.Shape", "Identity.Pos" ])

-- converts our type into a Coq type (a term) with new variables for all don't care values
toCoqType :: String
    -> [ Coq.Term ] -> IR.Type -> Converter ( Coq.Term, [ Coq.Qualid ] )
toCoqType varPrefix _ (IR.TypeVar _ _) = do
    x <- Coq.bare <$> freshCoqIdent varPrefix
    return ( Coq.Qualid x, [ x ] )
toCoqType varPrefix shapeAndPos (IR.TypeCon _ conName) = do
    entry <- lookupEntryOrFail NoSrcSpan IR.TypeScope conName
    return ( Coq.app (Coq.Qualid (entryIdent entry)) shapeAndPos, [] )
toCoqType varPrefix shapeAndPos (IR.TypeApp _ l r) = do
    ( l', varsl ) <- toCoqType varPrefix shapeAndPos l
    ( r', varsr ) <- toCoqType varPrefix shapeAndPos r
    return ( Coq.app l' [ r' ], varsl ++ varsr )

makeNFBindersAndReturnType'
    :: IR.Type -> Coq.Qualid -> Converter ( [ Coq.Binder ], Coq.Term )
makeNFBindersAndReturnType' t varName = do
    ( binders, sourceType, targetType ) <- makeNFBindersAndReturnType t
    let binders' = binders
            ++ [ (Coq.typedBinder' Coq.Explicit varName sourceType) ]
    let retType = applyFree targetType
    return ( binders', retType )

makeNFInstanceBindersAndReturnType
    :: IR.Type -> Converter ( [ Coq.Binder ], Coq.Term )
makeNFInstanceBindersAndReturnType t = do
    ( binders, sourceType, targetType ) <- makeNFBindersAndReturnType t
    let retType = Coq.app (Coq.Qualid (Coq.bare "Normalform"))
            (shapeAndPos ++ [ sourceType, targetType ])
    return ( binders, retType )

-- makes appropriate binders and return type for a (possibly local) nf' function
makeNFBindersAndReturnType
    :: IR.Type -> Converter ( [ Coq.Binder ], Coq.Term, Coq.Term )
makeNFBindersAndReturnType t = do
    ( sourceType, sourceVars ) <- toCoqType "a" shapeAndPos t
    ( targetType, targetVars ) <- toCoqType "b" idShapeAndPos t
    let constraints = map (buildConstraint "Normalform")
            (zipWith (\v1 v2 -> [ v1 ] ++ [ v2 ]) sourceVars targetVars)
    let binders = freeArgsBinders ++ [ typeBinder (sourceVars ++ targetVars) ]
            ++ constraints
    return ( binders, sourceType, targetType )

type TypeMap = IR.Type -> Maybe Coq.Qualid

emptyTypeMap :: TypeMap
emptyTypeMap = const Nothing

lookupType :: IR.Type -> TypeMap -> Maybe Coq.Qualid
lookupType = flip ($)

insertType :: IR.Type -> Coq.Qualid -> TypeMap -> TypeMap
insertType k v m = \t -> if k == t then Just v else m t
