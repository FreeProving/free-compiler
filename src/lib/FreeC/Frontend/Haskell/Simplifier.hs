-- | This module contains a converter from the @haskell-src-exts@ AST to
--   the intermediate representation used by the compiler.
--
--   The simplifier checks whether a given module complies with our assumptions
--   about the input file format and generates a fatal error message if
--   any Haskell feature is used that is not supported by the compiler.
--
--   In some places the simplifier also performs desugaring. For example,
--   infix operators are translated to regular function applications and
--   list literals to the application of the list constructors.
--
--  TODO warn user if reserved names like `error` or `undefined` are used
--       in declarations or as (type-) variable names.

module FreeC.Frontend.Haskell.Simplifier
  ( Simplifier
  , simplifyModuleWithComments
  , extractModName
  , simplifyDecls
  , simplifyType
  , simplifyTypeSchema
  , simplifyExpr
  )
where

import           Control.Monad                  ( unless
                                                , when
                                                )
import           Data.Composition               ( (.:) )
import           Data.List.Extra                ( concatUnzip3 )
import           Data.Maybe                     ( fromJust
                                                , fromMaybe
                                                , isJust
                                                )

import qualified Language.Haskell.Exts.Syntax  as HSE

import           FreeC.Environment.Fresh
import           FreeC.Frontend.IR.PragmaParser
import qualified FreeC.IR.Base.Prelude         as IR.Prelude
import           FreeC.IR.Reference             ( freeTypeVars )
import           FreeC.IR.SrcSpan
import           FreeC.IR.Subterm               ( findFirstSubterm )
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Monad.Converter
import           FreeC.Monad.Reporter

-------------------------------------------------------------------------------
-- State monad                                                               --
-------------------------------------------------------------------------------

-- | The simplifier is a special converter that converts the haskell@-src-exts@
--   AST to the simplified internal representation for Haskell modules.
--
--   During simplification the environment is usually empty (except for fresh
--   variables created by the simplifier).
type Simplifier = Converter

-------------------------------------------------------------------------------
-- Error reporting                                                           --
-------------------------------------------------------------------------------

-- | Creates a reporter that fails with an error message stating that
--   the given feature is not supported but required by the given Haskell
--   AST node.
notSupported
  :: HSE.Annotated a
  => String    -- ^ The feature (in plural) that is not supported.
  -> a SrcSpan -- ^ The node that is not supported.
  -> Simplifier r
notSupported feature = usageError (feature ++ " are not supported!")

-- | Reports that a feature is not supported and the given Haskell AST node
--   will therefore be ignored.
skipNotSupported
  :: HSE.Annotated a
  => String    -- ^ The feature (in plural) that is not supported.
  -> a SrcSpan -- ^ The node that is skipped.
  -> Simplifier ()
skipNotSupported feature = skipNotSupported' feature "will be skipped"

-- | Like 'skipNotSupported' but an additional parameter describes what is
--   done to skip the feature.
skipNotSupported'
  :: HSE.Annotated a
  => String    -- ^ The feature (in plural) that is not supported.
  -> String    -- ^ Description of what will be done to skip the feature.
  -> a SrcSpan -- ^ The node that is skipped.
  -> Simplifier ()
skipNotSupported' feature strategy node = report $ Message
  (HSE.ann node)
  Warning
  (feature ++ " are not supported and " ++ strategy ++ "!")

-- | Like 'notSupported' but refers to the `--transform-pattern-matching`
--   command line option to enable support for the future.
experimentallySupported
  :: HSE.Annotated a => String -> a SrcSpan -> Simplifier r
experimentallySupported feature = usageError
  (  feature
  ++ " are not supported!\n"
  ++ "Add the `--transform-pattern-matching` command line option to enable "
  ++ feature
  )

-- | Creates a reporter that fails with an error message stating that
--   a node that matches the given description was expected.
expected
  :: HSE.Annotated a
  => String    -- ^ A description of the expected node.
  -> a SrcSpan -- ^ The actual node.
  -> Simplifier r
expected description = usageError ("Expected " ++ description ++ ".")

-- | Creates a reporter that fails with the given error message.
usageError
  :: HSE.Annotated a
  => String    -- ^ The error message.
  -> a SrcSpan -- ^ The node that caused the error.
  -> Simplifier r
usageError message node = reportFatal $ Message (HSE.ann node) Error message

-- | Creates a reporter that reports a warning if the given condition is met.
warnIf
  :: HSE.Annotated a
  => Bool      -- ^ The conditiuon to test.
  -> String    -- ^ The waning to print if the condition is not met.
  -> a SrcSpan -- ^ The node that caused the warning.
  -> Simplifier ()
warnIf cond msg node = when cond (report $ Message (HSE.ann node) Warning msg)

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------

-- | Simplifies a module declaration.
--
--   The module must not contain any import declaration or pragmas. The export
--   list may be present but is ignored.
--
--   Only regular (non XML) modules are supported.
simplifyModuleWithComments
  :: HSE.Module SrcSpan -> [IR.Comment] -> Simplifier IR.Module
simplifyModuleWithComments ast@(HSE.Module srcSpan _ pragmas imports decls) comments
  = do
    unless (null pragmas) $ skipNotSupported "Module pragmas" (head pragmas)
    modName                             <- extractModName ast
    imports'                            <- mapM simplifyImport imports
    custumPragmas <- liftReporter $ parseCustomPragmas comments
    (typeDecls', typeSigs', funcDecls') <- simplifyDecls decls
    return
      (IR.Module { IR.modSrcSpan   = srcSpan
                 , IR.modName      = modName
                 , IR.modImports   = imports'
                 , IR.modTypeDecls = typeDecls'
                 , IR.modTypeSigs  = typeSigs'
                 , IR.modPragmas   = custumPragmas
                 , IR.modFuncDecls = funcDecls'
                 }
      )
simplifyModuleWithComments modDecl _ = notSupported "XML modules" modDecl

-- | Gets the name of the given module.
extractModName :: HSE.Module SrcSpan -> Simplifier IR.ModName
extractModName (HSE.Module _ modHead _ _ _) = do
  maybeModName <- mapM simplifyModuleHead modHead
  return (fromMaybe "Main" maybeModName)
extractModName modDecl = notSupported "XML modules" modDecl

-- | Gets the module name from the module head.
--
--   If present, the export list is ignored. We do not test whether only
--   defined functions and data types are exported. A warning is printed
--   to remind the user that the export list does not have any effect.
simplifyModuleHead :: HSE.ModuleHead SrcSpan -> Simplifier IR.ModName
simplifyModuleHead (HSE.ModuleHead _ (HSE.ModuleName _ modName) _ exports) = do
  warnIf (isJust exports) "Ignoring export list." (fromJust exports)
  return modName

-- | Gets the name of the module imported by the given import declaration.
simplifyImport :: HSE.ImportDecl SrcSpan -> Simplifier IR.ImportDecl
simplifyImport decl
  | HSE.importQualified decl = notSupported "Quallified imports" decl
  | HSE.importSrc decl = notSupported "Mutually recursive modules" decl
  | HSE.importSafe decl = notSupported "Safe imports" decl
  | isJust (HSE.importPkg decl) = notSupported
    "Imports with explicit package names"
    decl
  | isJust (HSE.importAs decl) = notSupported "Imports with aliases" decl
  | isJust (HSE.importSpecs decl) = do
    skipNotSupported' "Import specifications"
                      "everything will be imported"
                      (fromJust (HSE.importSpecs decl))
    simplifyImport decl { HSE.importSpecs = Nothing }
  | otherwise = case HSE.importModule decl of
    HSE.ModuleName srcSpan modName -> return (IR.ImportDecl srcSpan modName)

-------------------------------------------------------------------------------
-- Declarations                                                              --
-------------------------------------------------------------------------------

-- | Simplifies the given declarations.
simplifyDecls
  :: [HSE.Decl SrcSpan]
  -> Simplifier ([IR.TypeDecl], [IR.TypeSig], [IR.FuncDecl])
simplifyDecls decls = do
  decls' <- mapM simplifyDecl decls
  return (concatUnzip3 decls')

-- | Simplifies a declaration.
--
--   Only data type, type synonym, function declarations (including pattern
--   bindings for 0-ary functions) and type signatures are supported.
--   Fixity signatures are allowed but don't have a corresponding node in
--   the AST.
simplifyDecl
  :: HSE.Decl SrcSpan -> Simplifier ([IR.TypeDecl], [IR.TypeSig], [IR.FuncDecl])

-- Type synonym declarations.
simplifyDecl (HSE.TypeDecl srcSpan declHead typeExpr) = do
  (declIdent, typeArgs) <- simplifyDeclHead declHead
  typeExpr'             <- simplifyType typeExpr
  return ([IR.TypeSynDecl srcSpan declIdent typeArgs typeExpr'], [], [])

-- Data type declarations.
simplifyDecl (HSE.DataDecl srcSpan (HSE.DataType _) Nothing declHead conDecls [])
  = do
    (declIdent, typeArgs) <- simplifyDeclHead declHead
    conDecls'             <- mapM simplifyConDecl conDecls
    return ([IR.DataDecl srcSpan declIdent typeArgs conDecls'], [], [])

-- `newtype` declarations are not supported.
simplifyDecl decl@(HSE.DataDecl _ (HSE.NewType _) _ _ _ _) =
  notSupported "Newtype declarations" decl

-- Skip deriving and type class contexts.
simplifyDecl (HSE.DataDecl srcSpan dataType (Just context) declHead conDecls derivingClauses)
  = do
    skipNotSupported "Type class contexts" context
    simplifyDecl
      (HSE.DataDecl srcSpan dataType Nothing declHead conDecls derivingClauses)
simplifyDecl (HSE.DataDecl srcSpan dataType Nothing declHead conDecls (derivingDecl : _))
  = do
    skipNotSupported "Deriving clauses" derivingDecl
    simplifyDecl (HSE.DataDecl srcSpan dataType Nothing declHead conDecls [])

-- Function declarations.
simplifyDecl (HSE.FunBind _ [match]) = do
  funcDecl <- simplifyFuncDecl match
  return ([], [], [funcDecl])

-- Function declarations with more than one rule are not supported.
simplifyDecl decl@(HSE.FunBind _ _) =
  experimentallySupported "Function declarations with more than one rule" decl

-- Pattern-bindings for 0-ary functions.
simplifyDecl (HSE.PatBind srcSpan (HSE.PVar _ declName) (HSE.UnGuardedRhs _ rhs) Nothing)
  = do
    declIdent <- simplifyFuncDeclName declName
    rhs'      <- simplifyExpr rhs
    return ([], [], [IR.FuncDecl srcSpan declIdent [] [] Nothing rhs'])

-- The pattern-binding for a 0-ary function must not use guards or have a
-- where block.
simplifyDecl (HSE.PatBind _ (HSE.PVar _ _) rhss@(HSE.GuardedRhss _ _) _) =
  experimentallySupported "Guards" rhss
simplifyDecl (HSE.PatBind _ (HSE.PVar _ _) _ (Just binds)) =
  notSupported "Local declarations" binds

-- All other pattern-bindings are not supported.
simplifyDecl decl@(HSE.PatBind _ _ _ _) =
  notSupported "Pattern-bindings other than 0-ary function declarations" decl

-- Type signatures.
simplifyDecl (HSE.TypeSig srcSpan names typeExpr) = do
  names'      <- mapM simplifyFuncDeclName names
  typeSchema' <- simplifyTypeSchema typeExpr
  return ([], [IR.TypeSig srcSpan names' typeSchema'], [])

-- The user is allowed to specify fixities of custom infix declarations
-- and they are respected by the haskell-src-exts parser, but we do not
-- represent them in the AST.
simplifyDecl (     HSE.InfixDecl _ _ _ _ ) = return ([], [], [])

-- Skip pragmas.
simplifyDecl decl@(HSE.RulePragmaDecl _ _) = do
  skipNotSupported "RULES pragmas" decl
  return ([], [], [])
simplifyDecl decl@(HSE.DeprPragmaDecl _ _) = do
  skipNotSupported "DEPRECATED pragmas" decl
  return ([], [], [])
simplifyDecl decl@(HSE.WarnPragmaDecl _ _) = do
  skipNotSupported "WARNING pragmas" decl
  return ([], [], [])
simplifyDecl decl@(HSE.InlineSig _ _ _ _) = do
  skipNotSupported "INLINE pragmas" decl
  return ([], [], [])
simplifyDecl decl@(HSE.InlineConlikeSig _ _ _) = do
  skipNotSupported "INLINE CONLIKE pragmas" decl
  return ([], [], [])
simplifyDecl decl@(HSE.SpecSig _ _ _ _) = do
  skipNotSupported "SPECIALISE pragma" decl
  return ([], [], [])
simplifyDecl decl@(HSE.SpecInlineSig _ _ _ _ _) = do
  skipNotSupported "SPECIALISE INLINE pragmas" decl
  return ([], [], [])
simplifyDecl decl@(HSE.InstSig _ _) = do
  skipNotSupported "SPECIALISE instance pragmas" decl
  return ([], [], [])
simplifyDecl decl@(HSE.AnnPragma _ _) = do
  skipNotSupported "ANN pragmas" decl
  return ([], [], [])
simplifyDecl decl@(HSE.MinimalPragma _ _) = do
  skipNotSupported "MINIMAL pragmas" decl
  return ([], [], [])
simplifyDecl decl@(HSE.CompletePragma _ _ _) = do
  skipNotSupported "COMPLETE pragma" decl
  return ([], [], [])

-- All other declarations are not supported.
simplifyDecl decl@(HSE.TypeFamDecl _ _ _ _) = notSupported "Type families" decl
simplifyDecl decl@(HSE.ClosedTypeFamDecl _ _ _ _ _) =
  notSupported "Type families" decl
simplifyDecl decl@(HSE.DataFamDecl _ _ _ _) = notSupported "Type families" decl
simplifyDecl decl@(HSE.TypeInsDecl _ _ _  ) = notSupported "Type families" decl
simplifyDecl decl@(HSE.DataInsDecl _ _ _ _ _) =
  notSupported "Type families" decl
simplifyDecl decl@(HSE.GDataDecl _ _ _ _ _ _ _) =
  notSupported "GADT style declarations" decl
simplifyDecl decl@(HSE.GDataInsDecl _ _ _ _ _ _) =
  notSupported "GADT style declarations" decl
simplifyDecl decl@(HSE.ClassDecl _ _ _ _ _) = notSupported "Type classes" decl
simplifyDecl decl@(HSE.InstDecl _ _ _ _) = do
  skipNotSupported "Instance declarations" decl
  return ([], [], [])
simplifyDecl decl@(HSE.DerivDecl _ _ _ _) = do
  skipNotSupported "Deriving declarations" decl
  return ([], [], [])
simplifyDecl decl@(HSE.DefaultDecl _ _) = notSupported "Type classes" decl
simplifyDecl decl@(HSE.SpliceDecl _ _) = notSupported "Template Haskell" decl
simplifyDecl decl@(HSE.TSpliceDecl _ _) = notSupported "Template Haskell" decl
simplifyDecl decl@(HSE.PatSynSig _ _ _ _ _ _ _) =
  notSupported "Pattern synonyms" decl
simplifyDecl decl@(HSE.PatSyn _ _ _ _) = notSupported "Pattern synonyms" decl
simplifyDecl decl@(HSE.ForImp _ _ _ _ _ _) =
  notSupported "Foreign imports" decl
simplifyDecl decl@(HSE.ForExp _ _ _ _ _) = notSupported "Foreign exports" decl
simplifyDecl decl@(HSE.RoleAnnotDecl _ _ _) =
  notSupported "Role annotations" decl

-------------------------------------------------------------------------------
-- Data type and type synonym declarations                                   --
-------------------------------------------------------------------------------

-- | Gets the name the data type or type synonym declaration as well as the
--   type variables stored in the head of the declaration.
simplifyDeclHead
  :: HSE.DeclHead SrcSpan -> Simplifier (IR.DeclIdent, [IR.TypeVarDecl])
simplifyDeclHead (HSE.DHead _ declName) = do
  declIdent <- simplifyDeclName declName
  return (declIdent, [])
simplifyDeclHead (HSE.DHParen _ declHead          ) = simplifyDeclHead declHead
simplifyDeclHead (HSE.DHApp _ declHead typeVarBind) = do
  (declIdent, typeArgs) <- simplifyDeclHead declHead
  typeArg               <- simplifyTypeVarBind typeVarBind
  return (declIdent, typeArgs ++ [typeArg])
simplifyDeclHead declHead@(HSE.DHInfix _ _ _) =
  notSupported "Type operators" declHead

-- | Gets the name of a data type or type synonym declaration from the name
--   stored in the head of the declaration.
--
--   The name of the declaration must not be a symbol because type operators
--   are not supported.
simplifyDeclName :: HSE.Name SrcSpan -> Simplifier IR.DeclIdent
simplifyDeclName (HSE.Ident srcSpan ident) =
  return (IR.DeclIdent srcSpan (IR.UnQual (IR.Ident ident)))
simplifyDeclName sym@(HSE.Symbol _ _) = notSupported "Type operators" sym

-- | Gets the name of the type variable bound by the given binder.
--
--   The type variable must not be a symbol and the binder must not have
--   an explicit kind annotation.
simplifyTypeVarBind :: HSE.TyVarBind SrcSpan -> Simplifier IR.TypeVarDecl
simplifyTypeVarBind (HSE.UnkindedVar srcSpan (HSE.Ident _ ident)) =
  return (IR.TypeVarDecl srcSpan ident)
simplifyTypeVarBind typeVarBind@(HSE.UnkindedVar _ (HSE.Symbol _ _)) =
  notSupported "Type operators" typeVarBind
simplifyTypeVarBind typeVarBind@(HSE.KindedVar _ _ _) =
  notSupported "Kind annotations" typeVarBind

-------------------------------------------------------------------------------
-- Data type constructor declarations                                        --
-------------------------------------------------------------------------------

-- | Simplifies a constructor declaration of a data type declaration with
--   optional existential quantification binding. Existential quantification
--   bindings are not supported.
simplifyConDecl :: HSE.QualConDecl SrcSpan -> Simplifier IR.ConDecl
simplifyConDecl (HSE.QualConDecl _ Nothing Nothing conDecl) =
  simplifyConDecl' conDecl
simplifyConDecl conDecl@(HSE.QualConDecl _ (Just _) _ _) =
  notSupported "Existential quantifications" conDecl
simplifyConDecl conDecl@(HSE.QualConDecl _ _ (Just _) _) =
  notSupported "Type classes" conDecl

-- | Simplifies a constructor declaration of a data type declaration.
--
--   The constructor must be an ordinary data constructor. Infix constructors
--   @t1 \`C\` t2@ are treated as syntactic sugar for @C t1 t2@.
--   Record constructors and constructors whose name is a symbol (see
--   'simplifyConDeclName') are not supported.
simplifyConDecl' :: HSE.ConDecl SrcSpan -> Simplifier IR.ConDecl
simplifyConDecl' (HSE.ConDecl srcSpan conName args) = do
  conIdent <- simplifyConDeclName conName
  args'    <- mapM simplifyType args
  return (IR.ConDecl srcSpan conIdent args')
simplifyConDecl' (HSE.InfixConDecl pos t1 conName t2) =
  simplifyConDecl' (HSE.ConDecl pos conName [t1, t2])
simplifyConDecl' conDecl@(HSE.RecDecl _ _ _) =
  notSupported "Record constructors" conDecl

-- | Gets the name of a constructor declaration.
--
--   The name of the declaration must not be a symbol because custom
--   constructor operators are not supported.
simplifyConDeclName :: HSE.Name SrcSpan -> Simplifier IR.DeclIdent
simplifyConDeclName (HSE.Ident srcSpan ident) =
  return (IR.DeclIdent srcSpan (IR.UnQual (IR.Ident ident)))
simplifyConDeclName sym@(HSE.Symbol _ _) =
  notSupported "Constructor operator declarations" sym

-------------------------------------------------------------------------------
-- Function declarations                                        --
-------------------------------------------------------------------------------

-- | Simplifies the single rule of a function declaration.
simplifyFuncDecl :: HSE.Match SrcSpan -> Simplifier IR.FuncDecl
simplifyFuncDecl (HSE.Match srcSpan declName args (HSE.UnGuardedRhs _ rhs) Nothing)
  = do
    declIdent <- simplifyFuncDeclName declName
    args'     <- mapM simplifyVarPat args
    rhs'      <- simplifyExpr rhs
    return (IR.FuncDecl srcSpan declIdent [] args' Nothing rhs')

-- Function declarations with guards and where blocks are not supported.
simplifyFuncDecl (HSE.Match _ _ _ rhss@(HSE.GuardedRhss _ _) _) =
  experimentallySupported "Guards" rhss
simplifyFuncDecl (HSE.Match _ _ _ _ (Just binds)) =
  notSupported "Local declarations" binds

-- Infix function declarations are allowed when they have the for
-- @x \`f\` y = e@ but not @x (...) y = e@ (See 'simplifyFuncDeclName').
--
-- We treat @x1 \`f\` x2 ... xn@ as syntactic sugar for @f x1 x2 ... xn@.
simplifyFuncDecl (HSE.InfixMatch pos arg declName args rhs binds) =
  simplifyFuncDecl (HSE.Match pos declName (arg : args) rhs binds)

-- | Gets the name of a function declaration.
--
--   The name of the declaration must not be a symbol because custom operator
--   declarations are not supported.
simplifyFuncDeclName :: HSE.Name SrcSpan -> Simplifier IR.DeclIdent
simplifyFuncDeclName (HSE.Ident srcSpan ident) =
  return (IR.DeclIdent srcSpan (IR.UnQual (IR.Ident ident)))
simplifyFuncDeclName sym@(HSE.Symbol _ _) =
  notSupported "Operator declarations" sym

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------

-- | Simplifies the given type expression and abstracts it to a type schema.
--
--   If there is no explicit @forall@, all type variables that occur in the
--   type expression are abstracted aw. Otherwise, only the specified type
--   arguments are abstracted.
simplifyTypeSchema :: HSE.Type SrcSpan -> Simplifier IR.TypeSchema

-- With explicit @forall@.
simplifyTypeSchema (HSE.TyForall srcSpan (Just binds) Nothing typeExpr) = do
  typeArgs  <- mapM simplifyTypeVarBind binds
  typeExpr' <- simplifyType typeExpr
  return (IR.TypeSchema srcSpan typeArgs typeExpr')

-- Without explicit @forall@.
simplifyTypeSchema typeExpr = do
  typeExpr' <- simplifyType typeExpr
  let srcSpan         = IR.typeSrcSpan typeExpr'
      typeArgIdents   = freeTypeVars typeExpr'
      typeArgSrcSpans = map (findTypeArgSrcSpan typeExpr') typeArgIdents
      typeArgs        = zipWith IR.TypeVarDecl typeArgSrcSpans typeArgIdents
  return (IR.TypeSchema srcSpan typeArgs typeExpr')
 where
  -- | Finds the first occurrence of the type variable with the given name.
  --
  --   Returns 'NoSrcSpan' if 'findTypeArgSrcSpan'' returns @Nothing@.
  --   Since the type arguments have been extracted using 'freeTypeVars',
  --   'findTypeArgSrcSpan'' should never return @Nothing@.
  findTypeArgSrcSpan :: IR.Type -> IR.TypeVarIdent -> SrcSpan
  findTypeArgSrcSpan = fromMaybe NoSrcSpan .: flip findTypeArgSrcSpan'

  -- | Like 'findTypeArgSrcSpan' but returns @Nothing@ if there is
  --   no such type variable.
  findTypeArgSrcSpan' :: IR.TypeVarIdent -> IR.Type -> Maybe SrcSpan
  findTypeArgSrcSpan' = fmap IR.typeSrcSpan .: findFirstSubterm . isTypeVar

  -- | Tests whether the given type is the type variable with the given name.
  isTypeVar :: IR.TypeVarIdent -> IR.Type -> Bool
  isTypeVar typeVarIdent (IR.TypeVar _ typeVarIdent') =
    typeVarIdent == typeVarIdent'
  isTypeVar _ _ = False

-- | Simplifies the a type expression.
simplifyType :: HSE.Type SrcSpan -> Simplifier IR.Type

-- Function type @'t1' -> 't2'@.
simplifyType (HSE.TyFun srcSpan t1 t2) = do
  t1' <- simplifyType t1
  t2' <- simplifyType t2
  return (IR.FuncType srcSpan t1' t2')

-- Tuple type @('t1', ..., 'tn')@.
simplifyType (HSE.TyTuple srcSpan HSE.Boxed ts) = do
  let n = length ts
  ts' <- mapM simplifyType ts
  return (IR.typeConApp srcSpan (IR.Prelude.tupleTypeConName n) ts')

-- List type @['t']@.
simplifyType (HSE.TyList srcSpan t) = do
  t' <- simplifyType t
  return (IR.typeConApp srcSpan IR.Prelude.listTypeConName [t'])

-- Type constructor application @'t1' 't2'@.
simplifyType (HSE.TyApp srcSpan t1 t2) = do
  t1' <- simplifyType t1
  t2' <- simplifyType t2
  return (IR.TypeApp srcSpan t1' t2')

-- Type variable @'ident'@.
simplifyType (HSE.TyVar srcSpan (HSE.Ident _ ident)) =
  return (IR.TypeVar srcSpan ident)

-- Type constructor @'ident'@.
simplifyType (HSE.TyCon srcSpan name) = do
  name' <- simplifyTypeConName name
  return (IR.TypeCon srcSpan name')

-- Type wrapped in parentheses @('t')@.
simplifyType (HSE.TyParen _ t                        ) = simplifyType t

-- Skip type class contexts.
simplifyType (HSE.TyForall _ Nothing (Just context) t) = do
  skipNotSupported "Type class contexts" context
  simplifyType t

-- Not supported types.
simplifyType ty@(HSE.TyForall _ _ _ _) =
  notSupported "Explicit type variable quantifications" ty
simplifyType ty@(HSE.TyTuple _ HSE.Unboxed _) =
  notSupported "Unboxed tuples" ty
simplifyType ty@(HSE.TyUnboxedSum _ _) = notSupported "Unboxed sums" ty
simplifyType ty@(HSE.TyParArray   _ _) = notSupported "Parallel arrays" ty
simplifyType ty@(HSE.TyKind _ _ _) =
  notSupported "Types with explicit kind signatures" ty
simplifyType ty@(HSE.TyStar _) = notSupported "Kinds" ty
simplifyType ty@(HSE.TyVar _ (HSE.Symbol _ _)) =
  notSupported "Type operators" ty
simplifyType ty@(HSE.TyPromoted _ _ ) = notSupported "Type operators" ty
simplifyType ty@(HSE.TyInfix _ _ _ _) = notSupported "Type operators" ty
simplifyType ty@(HSE.TyEquals _ _ _) =
  notSupported "Type equality predicates" ty
simplifyType ty@(HSE.TySplice _ _  ) = notSupported "Template Haskell" ty
simplifyType ty@(HSE.TyBang _ _ _ _) = notSupported "Striktness annotations" ty
simplifyType ty@(HSE.TyWildCard _ _) = notSupported "Type wildcards" ty
simplifyType ty@(HSE.TyQuasiQuote _ _ _) =
  notSupported "Quasiquotation types" ty

-- | Simplifies the name of a build-in or user defined type constructor.
simplifyTypeConName :: HSE.QName SrcSpan -> Simplifier IR.TypeConName
simplifyTypeConName (HSE.UnQual _ (HSE.Ident _ ident)) =
  return (IR.UnQual (IR.Ident ident))
simplifyTypeConName (HSE.Qual _ (HSE.ModuleName _ modName) (HSE.Ident _ ident))
  = return (IR.Qual modName (IR.Ident ident))
simplifyTypeConName (HSE.Special _ (HSE.UnitCon _)) =
  return IR.Prelude.unitTypeConName
simplifyTypeConName (HSE.Special _ (HSE.ListCon _)) =
  return IR.Prelude.listTypeConName
simplifyTypeConName (HSE.Special _ (HSE.TupleCon _ HSE.Boxed n)) =
  return (IR.Prelude.tupleTypeConName n)

-- Not supported type constructor names.
simplifyTypeConName name@(HSE.UnQual _ (HSE.Symbol _ _)) =
  notSupported "Type operators" name
simplifyTypeConName name@(HSE.Qual _ _ (HSE.Symbol _ _)) =
  notSupported "Type operators" name
simplifyTypeConName name@(HSE.Special _ (HSE.FunCon _)) =
  notSupported "Function type constructors" name
simplifyTypeConName name@(HSE.Special _ (HSE.TupleCon _ HSE.Unboxed _)) =
  notSupported "Unboxed tuples" name
simplifyTypeConName name@(HSE.Special _ (HSE.UnboxedSingleCon _)) =
  notSupported "Unboxed tuples" name
simplifyTypeConName name@(HSE.Special _ (HSE.ExprHole _)) =
  notSupported "Expression holes" name
simplifyTypeConName name@(HSE.Special _ (HSE.Cons _)) = usageError
  "The data constructor (:) cannot be used as a type constructor!"
  name

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Simplifies an expression.
simplifyExpr :: HSE.Exp SrcSpan -> Simplifier IR.Expr

-- Error terms are regular functions but need to be handled differently.
simplifyExpr (HSE.Var srcSpan (HSE.UnQual _ (HSE.Ident _ "undefined"))) =
  return (IR.Undefined srcSpan Nothing)
simplifyExpr (HSE.App srcSpan (HSE.Var _ (HSE.UnQual _ (HSE.Ident _ "error"))) arg)
  = case arg of
    (HSE.Lit _ (HSE.String _ msg _)) ->
      return (IR.ErrorExpr srcSpan msg Nothing)
    _ -> notSupported "Non-literal error messages" arg
simplifyExpr expr@(HSE.Var _ (HSE.UnQual _ (HSE.Ident _ "error"))) =
  usageError "The function 'error' must be applied immediately." expr

-- Parenthesis.
simplifyExpr (HSE.Paren _       expr) = simplifyExpr expr

-- Variables.
simplifyExpr (HSE.Var   srcSpan name) = do
  name' <- simplifyVarName name
  return (IR.Var srcSpan name' Nothing)

-- Constructors.
simplifyExpr (HSE.Con srcSpan name) = do
  name' <- simplifyConName name
  return (IR.Con srcSpan name' Nothing)

-- Integer literals.
simplifyExpr (HSE.Lit srcSpan (HSE.Int _ value _)) =
  return (IR.IntLiteral srcSpan value Nothing)

-- Tuples.
simplifyExpr (HSE.Tuple srcSpan HSE.Boxed es) = do
  let n = length es
  es' <- mapM simplifyExpr es
  return (IR.conApp srcSpan (IR.Prelude.tupleConName n) es')

-- List literals are converted to a chain of 'IR.Prelude.consConName'
-- applications with a trailing 'IR.Prelude.nilConName'. All generated
-- constructors refer to the same source span of the original list literal.
simplifyExpr (HSE.List srcSpan exprs) = do
  let nil  = IR.Con srcSpan IR.Prelude.nilConName Nothing
      cons = IR.Con srcSpan IR.Prelude.consConName Nothing
  exprs' <- mapM simplifyExpr exprs
  return (foldr (IR.untypedApp srcSpan . IR.untypedApp srcSpan cons) nil exprs')

-- Function applications.
simplifyExpr (HSE.App srcSpan e1 e2) = do
  e1' <- simplifyExpr e1
  e2' <- simplifyExpr e2
  return (IR.App srcSpan e1' e2' Nothing)

-- Infix operator, function or constructor applications.
simplifyExpr (HSE.InfixApp srcSpan e1 op e2) = do
  e1' <- simplifyExpr e1
  op' <- simplifyOp op
  e2' <- simplifyExpr e2
  return (IR.app srcSpan op' [e1', e2'])

-- Partial infix applications. For right sections we need to introduce a
-- fresh variable for the missing left argument using a lambda abstraction.
simplifyExpr (HSE.LeftSection srcSpan e1 op) = do
  e1' <- simplifyExpr e1
  op' <- simplifyOp op
  return (IR.App srcSpan op' e1' Nothing)
simplifyExpr (HSE.RightSection srcSpan op e2) = do
  x   <- freshHaskellIdent freshArgPrefix
  op' <- simplifyOp op
  e2' <- simplifyExpr e2
  let x'  = IR.VarPat srcSpan x Nothing
      e1' = IR.Var srcSpan (IR.UnQual (IR.Ident x)) Nothing
  return (IR.Lambda srcSpan [x'] (IR.app srcSpan op' [e1', e2']) Nothing)

-- Negation.
simplifyExpr (HSE.NegApp srcSpan expr) = do
  expr' <- simplifyExpr expr
  return (IR.varApp srcSpan IR.Prelude.negateOpName [expr'])

-- Lambda abstractions.
simplifyExpr (HSE.Lambda srcSpan args expr) = do
  args' <- mapM simplifyVarPat args
  expr' <- simplifyExpr expr
  return (IR.Lambda srcSpan args' expr' Nothing)

-- Conditional expressions.
simplifyExpr (HSE.If srcSpan e1 e2 e3) = do
  e1' <- simplifyExpr e1
  e2' <- simplifyExpr e2
  e3' <- simplifyExpr e3
  return (IR.If srcSpan e1' e2' e3' Nothing)

-- Case expressions.
simplifyExpr (HSE.Case srcSpan expr alts) = do
  expr' <- simplifyExpr expr
  alts' <- mapM simplifyAlt alts
  return (IR.Case srcSpan expr' alts' Nothing)

-- Type signatures.
simplifyExpr (HSE.ExpTypeSig srcSpan expr typeExpr) = do
  expr' <- simplifyExpr expr
  case IR.exprTypeSchema expr' of
    Nothing -> do
      typeSchema <- simplifyTypeSchema typeExpr
      return expr' { IR.exprTypeSchema = Just typeSchema }
    Just _ -> do
      report
        $ Message srcSpan Warning
        $ "Type signature is redundant and will be ignored."
      return expr'

-- Skip pragmas.
simplifyExpr pragma@(HSE.CorePragma _ _ expr) = do
  skipNotSupported "CORE pragmas" pragma
  simplifyExpr expr
simplifyExpr pragma@(HSE.SCCPragma _ _ expr) = do
  skipNotSupported "SCC pragmas" pragma
  simplifyExpr expr
simplifyExpr pragma@(HSE.GenPragma _ _ _ _ expr) = do
  skipNotSupported "GENERATED pragmas" pragma
  simplifyExpr expr

-- Not supported expressions.
simplifyExpr expr@(HSE.OverloadedLabel _ _) =
  notSupported "Overloaded labels" expr
simplifyExpr expr@(HSE.IPVar _ _) =
  notSupported "Implicit parameter variables" expr
simplifyExpr expr@(HSE.Let _ _ _) = notSupported "Local declarations" expr
simplifyExpr expr@(HSE.MultiIf _ _) =
  notSupported "Multi-Way if expressions" expr
simplifyExpr expr@(HSE.Do  _ _) = notSupported "do-expressions" expr
simplifyExpr expr@(HSE.MDo _ _) = notSupported "mdo-expressions" expr
simplifyExpr expr@(HSE.Tuple _ HSE.Unboxed _) =
  notSupported "Unboxed tuples" expr
simplifyExpr expr@(HSE.UnboxedSum _ _ _ _) = notSupported "Unboxed sums" expr
simplifyExpr expr@(HSE.TupleSection _ _ _) = notSupported "Tuple sections" expr
simplifyExpr expr@(HSE.ParArray _ _      ) = notSupported "Parallel arrays" expr
simplifyExpr expr@(HSE.RecConstr _ _ _) =
  notSupported "Record constructors" expr
simplifyExpr expr@(HSE.RecUpdate _ _ _   ) = notSupported "Record updates" expr
simplifyExpr expr@(HSE.EnumFrom _ _      ) = notSupported "Enumerations" expr
simplifyExpr expr@(HSE.EnumFromTo   _ _ _) = notSupported "Enumerations" expr
simplifyExpr expr@(HSE.EnumFromThen _ _ _) = notSupported "Enumerations" expr
simplifyExpr expr@(HSE.EnumFromThenTo _ _ _ _) =
  notSupported "Enumerations" expr
simplifyExpr expr@(HSE.ParArrayFromTo _ _ _) =
  notSupported "Parallel arrays" expr
simplifyExpr expr@(HSE.ParArrayFromThenTo _ _ _ _) =
  notSupported "Parallel arrays" expr
simplifyExpr expr@(HSE.ListComp _ _ _) =
  notSupported "List comprehensions" expr
simplifyExpr expr@(HSE.ParComp _ _ _) =
  notSupported "Parallel list comprehensions" expr
simplifyExpr expr@(HSE.ParArrayComp _ _ _) =
  notSupported "Parallel array comprehensions" expr
simplifyExpr expr@(HSE.VarQuote   _ _  ) = notSupported "Template Haskell" expr
simplifyExpr expr@(HSE.TypQuote   _ _  ) = notSupported "Template Haskell" expr
simplifyExpr expr@(HSE.BracketExp _ _  ) = notSupported "Template Haskell" expr
simplifyExpr expr@(HSE.SpliceExp  _ _  ) = notSupported "Template Haskell" expr
simplifyExpr expr@(HSE.QuasiQuote _ _ _) = notSupported "Quasiquotation" expr
simplifyExpr expr@(HSE.TypeApp _ _) =
  notSupported "Visible type applications" expr
simplifyExpr expr@(HSE.XTag _ _ _ _ _) = notSupported "XML elements" expr
simplifyExpr expr@(HSE.XETag _ _ _ _ ) = notSupported "XML elements" expr
simplifyExpr expr@(HSE.XPcdata   _ _ ) = notSupported "XML elements" expr
simplifyExpr expr@(HSE.XExpTag   _ _ ) = notSupported "XML elements" expr
simplifyExpr expr@(HSE.XChildTag _ _ ) = notSupported "XML elements" expr
simplifyExpr expr@(HSE.Proc _ _ _    ) = notSupported "Arrow expressions" expr
simplifyExpr expr@(HSE.LeftArrApp _ _ _) =
  notSupported "Arrow expressions" expr
simplifyExpr expr@(HSE.RightArrApp _ _ _) =
  notSupported "Arrow expressions" expr
simplifyExpr expr@(HSE.LeftArrHighApp _ _ _) =
  notSupported "Arrow expressions" expr
simplifyExpr expr@(HSE.RightArrHighApp _ _ _) =
  notSupported "Arrow expressions" expr
simplifyExpr expr@(HSE.ArrOp _ _) = notSupported "Arrow control operators" expr
simplifyExpr expr@(HSE.LCase _ _) = notSupported "Lambda case expressions" expr

-- Not supported literals.
simplifyExpr expr@(HSE.Lit _ (HSE.Char _ _ _)) =
  notSupported "Character literals" expr
simplifyExpr expr@(HSE.Lit _ (HSE.String _ _ _)) =
  notSupported "String literals" expr
simplifyExpr expr@(HSE.Lit _ (HSE.Frac _ _ _)) =
  notSupported "Floating point literals" expr
simplifyExpr expr@(HSE.Lit _ (HSE.PrimInt _ _ _)) =
  notSupported "Unboxed integer literals" expr
simplifyExpr expr@(HSE.Lit _ (HSE.PrimWord _ _ _)) =
  notSupported "Unboxed word literals" expr
simplifyExpr expr@(HSE.Lit _ (HSE.PrimFloat _ _ _)) =
  notSupported "Unboxed float literals" expr
simplifyExpr expr@(HSE.Lit _ (HSE.PrimDouble _ _ _)) =
  notSupported "Unboxed double literals" expr
simplifyExpr expr@(HSE.Lit _ (HSE.PrimChar _ _ _)) =
  notSupported "Unboxed character literals" expr
simplifyExpr expr@(HSE.Lit _ (HSE.PrimString _ _ _)) =
  notSupported "Unboxed string literals" expr

-- | Simplifies an infix operator.
simplifyOp :: HSE.QOp SrcSpan -> Simplifier IR.Expr
simplifyOp (HSE.QVarOp srcSpan name) =
  IR.untypedVar srcSpan <$> simplifyVarName name
simplifyOp (HSE.QConOp srcSpan name) =
  IR.untypedCon srcSpan <$> simplifyConName name

-- | Simplifies an unqualified name.
simplifyName :: HSE.Name SrcSpan -> Simplifier IR.Name
simplifyName (HSE.Ident  _ ident) = return (IR.Ident ident)
simplifyName (HSE.Symbol _ sym  ) = return (IR.Symbol sym)

-- | Gets the name of a variable, defined function or predefined function (e.g.
--   @(+)@).
simplifyVarName :: HSE.QName SrcSpan -> Simplifier IR.VarName
simplifyVarName (HSE.UnQual _ name) = IR.UnQual <$> simplifyName name
simplifyVarName (HSE.Qual _ (HSE.ModuleName _ modName) name) =
  IR.Qual modName <$> simplifyName name
simplifyVarName name@(HSE.Special _ _) =
  usageError "Constructors cannot be used as variables!" name

-- | Gets the name of a build-in or user defined constructor.
simplifyConName :: HSE.QName SrcSpan -> Simplifier IR.ConName
simplifyConName (HSE.UnQual _ name) = IR.UnQual <$> simplifyName name
simplifyConName (HSE.Qual _ (HSE.ModuleName _ modName) name) =
  IR.Qual modName <$> simplifyName name
simplifyConName (HSE.Special _ (HSE.UnitCon _)) = return IR.Prelude.unitConName
simplifyConName (HSE.Special _ (HSE.ListCon _)) = return IR.Prelude.nilConName
simplifyConName (HSE.Special _ (HSE.Cons    _)) = return IR.Prelude.consConName
simplifyConName (HSE.Special _ (HSE.TupleCon _ HSE.Boxed n)) =
  return (IR.Prelude.tupleConName n)

-- Not supported constructor names.
simplifyConName name@(HSE.Special _ (HSE.FunCon _)) =
  usageError "Function type constructor cannot be used as a constructor!" name
simplifyConName name@(HSE.Special _ (HSE.TupleCon _ HSE.Unboxed _)) =
  notSupported "Unboxed tuples" name
simplifyConName name@(HSE.Special _ (HSE.UnboxedSingleCon _)) =
  notSupported "Unboxed tuples" name
simplifyConName name@(HSE.Special _ (HSE.ExprHole _)) =
  notSupported "Expression holes" name

-- | Simplifies a variable pattern (e.g. the parameters of a lambda abstraction
--   or function declaration).
--
--  Parenthesis are ignored.
simplifyVarPat :: HSE.Pat SrcSpan -> Simplifier IR.VarPat
simplifyVarPat (HSE.PVar srcSpan (HSE.Ident _ ident)) =
  return (IR.VarPat srcSpan ident Nothing)
simplifyVarPat pat = expected "variable pattern" pat

-- Simplifies a constructor pattern.
--
-- Returns the simplified name of the matched constructor and it's variable
-- pattern arguments.
--
-- The pattern is also allowed to be a list (i.e. @x : xs@ or @[]@), unit (i.e.
-- @()@) or pair (i.e. @(x, y)@) constructor pattern, however the list pattern
-- @[x1, ..., xn]@ is not allowed.
--  Parentheses are ignored.
simplifyConPat :: HSE.Pat SrcSpan -> Simplifier (IR.ConPat, [IR.VarPat])

-- Ignore parentheses.
simplifyConPat (HSE.PParen _ pat    ) = simplifyConPat pat

-- Regular constructor pattern.
simplifyConPat (HSE.PApp _ name args) = do
  name' <- simplifyConName name
  vars  <- mapM simplifyVarPat args
  return (IR.ConPat (HSE.ann name) name', vars)

-- Infix constructor pattern (e.g. @x : xs@).
simplifyConPat (HSE.PInfixApp _ p1 name p2) = do
  v1    <- simplifyVarPat p1
  name' <- simplifyConName name
  v2    <- simplifyVarPat p2
  return (IR.ConPat (HSE.ann name) name', [v1, v2])

-- Tuple constructor pattern.
simplifyConPat (HSE.PTuple srcSpan HSE.Boxed ps) = do
  let n = length ps
  vs <- mapM simplifyVarPat ps
  return (IR.ConPat srcSpan (IR.Prelude.tupleConName n), vs)

-- Other tuple constructor patterns are not supported.
simplifyConPat pat@(HSE.PTuple _ HSE.Unboxed _) =
  notSupported "Unboxed tuples" pat

-- The list notation pattern @[x1, ..., xn]@ is not supported because it is
-- not a shallow pattern (i.e. cannot be represented as a pair of constructor
-- name and variable patterns).
-- But we allow the empty list pattern @[]@.
simplifyConPat (HSE.PList srcSpan []) =
  return (IR.ConPat srcSpan IR.Prelude.nilConName, [])
simplifyConPat pat@(HSE.PList _ _) =
  experimentallySupported "List notation patterns" pat

-- Record constructors are not supported.
simplifyConPat pat@(HSE.PRec _ _ _) = notSupported "Record constructors" pat

-- All other non-constructor patterns are not supported (e.g. variable,
-- wildcard or as-patterns etc.).
simplifyConPat pat                  = expected "constructor pattern" pat

-- | Simplifies an alternative of a case expression.
simplifyAlt :: HSE.Alt SrcSpan -> Simplifier IR.Alt
simplifyAlt (HSE.Alt srcSpan pat (HSE.UnGuardedRhs _ expr) Nothing) = do
  (con, vars) <- simplifyConPat pat
  expr'       <- simplifyExpr expr
  return (IR.Alt srcSpan con vars expr')
simplifyAlt (HSE.Alt _ _ rhss@(HSE.GuardedRhss _ _) _) =
  experimentallySupported "Guards" rhss
simplifyAlt (HSE.Alt _ _ _ (Just binds)) =
  notSupported "Local declarations" binds
