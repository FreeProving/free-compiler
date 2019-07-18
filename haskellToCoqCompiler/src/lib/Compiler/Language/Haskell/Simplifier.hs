-- | This module contains a converter from the @haskell-src-exts@ AST to
--   the simplified AST used by the compiler.
--
--   The simplifier checks whether a given module complies with our assumtions
--   about the input file format and generates a fatal error message if
--   any Hasell feature is used that is not supported by the compiler.
--
--   In some places the simplifier also performs desugaring to reduce the
--   number of constructors in the simple AST.
--
--  TODO warn user if reserved names like `error` or `undefined` are used
--       in declarations or as (type-) variable names.

module Compiler.Language.Haskell.Simplifier
  ( simplifyModule
  , simplifyDecl
  , simplifyType
  , simplifyExpr
  )
where

import           Data.Maybe                     ( isJust
                                                , fromJust
                                                )
import           Control.Monad                  ( when )

import qualified Language.Haskell.Exts.Syntax  as H

import           Compiler.Reporter
import qualified Compiler.Language.Haskell.SimpleAST
                                               as HS
import           Compiler.SrcSpan

-------------------------------------------------------------------------------
-- Error reporting                                                           --
-------------------------------------------------------------------------------

-- | Creates a reporter that fails with an error message stating that
--   the given feature is not supported but required by the given Haskell
--   AST node.
notSupported
  :: H.Annotated a
  => String    -- ^ The feature (in plural) that is not supported.
  -> a SrcSpan -- ^ The node that is not supported.
  -> Reporter r
notSupported feature = usageError (feature ++ " are not supported!")

-- | Creates a reporter that fails with an error message stating that
--   a node that matches the given description was expected.
expected
  :: H.Annotated a
  => String    -- ^ A description of the expected node.
  -> a SrcSpan -- ^ The actual node.
  -> Reporter r
expected description = usageError ("Expected " ++ description ++ ".")

-- | Creates a reporter that fails with the given error message.
usageError
  :: H.Annotated a
  => String    -- ^ The error message.
  -> a SrcSpan -- ^ The node that caused the error.
  -> Reporter r
usageError message node =
  reportFatal $ Message (Just (H.ann node)) Error message

-- | Creates a reporter that reports a warning if the given condition is met.
warnIf
  :: H.Annotated a
  => Bool      -- ^ The condition to test.
  -> String    -- ^ The waning to print if the condition is not met.
  -> a SrcSpan -- ^ The node that caused the warning.
  -> Reporter ()
warnIf cond msg node =
  when cond (report $ Message (Just (H.ann node)) Warning msg)

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------

-- | Simplifies a module declaration.
--
--   The module must not contain any import declaration or pragmas. The export
--   list may be present but is ignored.
--
--   Only regular (non XML) modules are supported.
simplifyModule :: H.Module SrcSpan -> Reporter HS.Module
simplifyModule (H.Module srcSpan modHead pragmas imports decls)
  | not (null pragmas) = notSupported "Module pragmas" (head pragmas)
  | not (null imports) = notSupported "Module imports" (head imports)
  | otherwise = do
    modIdent <- mapM simplifyModuleHead modHead
    decls'   <- mapM simplifyDecl decls
    return (HS.Module srcSpan modIdent decls')
simplifyModule modDecl = notSupported "XML modules" modDecl

-- | Gets the module name from the module head.
--
--   If present, the export list is ignored. We do not test whether only
--   defined functions and data types are exported. A warning is printed
--   to remind the user that the export list does not have any effect.
simplifyModuleHead :: H.ModuleHead SrcSpan -> Reporter HS.ModuleIdent
simplifyModuleHead (H.ModuleHead _ (H.ModuleName _ modIdent) _ exports) = do
  warnIf (isJust exports) "Ignoring export list." (fromJust exports)
  return modIdent

-------------------------------------------------------------------------------
-- Declarations                                                              --
-------------------------------------------------------------------------------

-- | Simplifies a declaration.
--
--   Only data type, type synonym, function declarations (including pattern
--   bindings for 0-ary functions) and type signatures are supported.
simplifyDecl :: H.Decl SrcSpan -> Reporter HS.Decl

-- Type synonym declarations.
simplifyDecl (H.TypeDecl srcSpan declHead typeExpr) = do
  (declIdent, typeVars) <- simplifyDeclHead declHead
  typeExpr'             <- simplifyType typeExpr
  return (HS.TypeDecl srcSpan declIdent typeVars typeExpr')

-- Data type declarations.
simplifyDecl (H.DataDecl srcSpan (H.DataType _) Nothing declHead conDecls []) =
  do
    (declIdent, typeVars) <- simplifyDeclHead declHead
    conDecls'             <- mapM simplifyConDecl conDecls
    return (HS.DataDecl srcSpan declIdent typeVars conDecls')

-- Not supported data declarations.
simplifyDecl decl@(H.DataDecl _ (H.NewType _) _ _ _ _) =
  notSupported "Newtype declarations" decl
simplifyDecl decl@(H.DataDecl _ _ (Just _) _ _ _) =
  notSupported "Type classes" decl
simplifyDecl decl@(H.DataDecl _ _ _ _ _ (_ : _)) =
  notSupported "Type classes" decl

-- Function declarations.
simplifyDecl (H.FunBind _ [match]) = simplifyFuncDecl match

-- Function declarations with more than one rule are not supported.
simplifyDecl decl@(H.FunBind _ _) =
  notSupported "Function declarations with more than one rule" decl

-- Pattern-bindings for 0-ary functions.
simplifyDecl (H.PatBind srcSpan (H.PVar _ declName) (H.UnGuardedRhs _ expr) Nothing)
  = do
    declIdent <- simplifyFuncDeclName declName
    expr'     <- simplifyExpr expr
    return (HS.FuncDecl srcSpan declIdent [] expr')

-- The pattern-binding for a 0-ary function must not use guards are have a
-- where block.
simplifyDecl (H.PatBind _ (H.PVar _ _) rhss@(H.GuardedRhss _ _) _) = do
  notSupported "Guards" rhss
simplifyDecl (H.PatBind _ (H.PVar _ _) _ (Just binds)) = do
  notSupported "Local declarations" binds

-- All other pattern-bindings are not supported.
simplifyDecl decl@(H.PatBind _ _ _ _) =
  notSupported "Pattern-bindings other than 0-ary function declarations" decl

-- Type signatures.
simplifyDecl (H.TypeSig srcSpan names typeExpr) = do
  names'    <- mapM simplifyFuncDeclName names
  typeExpr' <- simplifyType typeExpr
  return (HS.TypeSig srcSpan names' typeExpr')

-- The user is allowed to specify fixities of custom infix declarations
-- and they are respected by the haskell-src-exts parser.
simplifyDecl (H.InfixDecl srcSpan assoc precedence ops) = do
  assoc' <- simplifyAssoc assoc
  ops'   <- mapM simplifyUnqualOp ops
  return (HS.FixitySig srcSpan assoc' precedence ops')

-- All other declarations are not supported.
simplifyDecl decl@(H.TypeFamDecl _ _ _ _) = notSupported "Type families" decl
simplifyDecl decl@(H.ClosedTypeFamDecl _ _ _ _ _) =
  notSupported "Type families" decl
simplifyDecl decl@(H.DataFamDecl _ _ _ _  ) = notSupported "Type families" decl
simplifyDecl decl@(H.TypeInsDecl _ _ _    ) = notSupported "Type families" decl
simplifyDecl decl@(H.DataInsDecl _ _ _ _ _) = notSupported "Type families" decl
simplifyDecl decl@(H.GDataDecl _ _ _ _ _ _ _) =
  notSupported "GADT style declarations" decl
simplifyDecl decl@(H.GDataInsDecl _ _ _ _ _ _) =
  notSupported "GADT style declarations" decl
simplifyDecl decl@(H.ClassDecl _ _ _ _ _) = notSupported "Type classes" decl
simplifyDecl decl@(H.InstDecl  _ _ _ _  ) = notSupported "Type classes" decl
simplifyDecl decl@(H.DerivDecl _ _ _ _  ) = notSupported "Type classes" decl
simplifyDecl decl@(H.DefaultDecl _ _    ) = notSupported "Type classes" decl
simplifyDecl decl@(H.SpliceDecl  _ _    ) = notSupported "Template Haskell" decl
simplifyDecl decl@(H.PatSynSig _ _ _ _ _ _ _) =
  notSupported "Pattern synonyms" decl
simplifyDecl decl@(H.PatSyn _ _ _ _) = notSupported "Pattern synonyms" decl
simplifyDecl decl@(H.ForImp _ _ _ _ _ _) = notSupported "Foreign imports" decl
simplifyDecl decl@(H.ForExp _ _ _ _ _) = notSupported "Foreign exports" decl
simplifyDecl decl@(H.RulePragmaDecl _ _     ) = notSupported "Pragmas" decl
simplifyDecl decl@(H.DeprPragmaDecl _ _     ) = notSupported "Pragmas" decl
simplifyDecl decl@(H.WarnPragmaDecl _ _     ) = notSupported "Pragmas" decl
simplifyDecl decl@(H.InlineSig _ _ _ _      ) = notSupported "Pragmas" decl
simplifyDecl decl@(H.InlineConlikeSig _ _ _ ) = notSupported "Pragmas" decl
simplifyDecl decl@(H.SpecSig _ _ _ _        ) = notSupported "Pragmas" decl
simplifyDecl decl@(H.SpecInlineSig _ _ _ _ _) = notSupported "Pragmas" decl
simplifyDecl decl@(H.InstSig       _ _      ) = notSupported "Pragmas" decl
simplifyDecl decl@(H.AnnPragma     _ _      ) = notSupported "Pragmas" decl
simplifyDecl decl@(H.MinimalPragma _ _      ) = notSupported "Pragmas" decl
simplifyDecl decl@(H.CompletePragma _ _ _   ) = notSupported "Pragmas" decl
simplifyDecl decl@(H.RoleAnnotDecl _ _ _) =
  notSupported "Role annotations" decl

-------------------------------------------------------------------------------
-- Infix operator fixity declarations                                        --
-------------------------------------------------------------------------------

-- | Converts the data type that is used to mark the operator associativity
--   in operator fixity declarations.
simplifyAssoc :: H.Assoc SrcSpan -> Reporter HS.Assoc
simplifyAssoc (H.AssocNone  _) = return HS.AssocNone
simplifyAssoc (H.AssocLeft  _) = return HS.AssocLeft
simplifyAssoc (H.AssocRight _) = return HS.AssocRight

-- | Simplifies an infix operator from a fixity declaration.
simplifyUnqualOp :: H.Op SrcSpan -> Reporter HS.Op
simplifyUnqualOp (H.VarOp srcSpan name) = do
  HS.DeclIdent _ ident <- simplifyFuncDeclName name
  return (HS.VarOp srcSpan (HS.Ident ident))
simplifyUnqualOp (H.ConOp srcSpan name) = do
  HS.DeclIdent _ ident <- simplifyConDeclName name
  return (HS.ConOp srcSpan (HS.Ident ident))

-------------------------------------------------------------------------------
-- Data type and type synonym declarations                                   --
-------------------------------------------------------------------------------

-- | Gets the name the data type or type synonym declaration as well as the
--   type variables stored in the head of the declaration.
simplifyDeclHead
  :: H.DeclHead SrcSpan -> Reporter (HS.DeclIdent, [HS.TypeVarDecl])
simplifyDeclHead (H.DHead _ declName) = do
  declIdent <- simplifyDeclName declName
  return (declIdent, [])
simplifyDeclHead (H.DHParen _ declHead          ) = simplifyDeclHead declHead
simplifyDeclHead (H.DHApp _ declHead typeVarBind) = do
  (declIdent, typeVars) <- simplifyDeclHead declHead
  typeVar               <- simplifyTypeVarBind typeVarBind
  return (declIdent, typeVars ++ [typeVar])
simplifyDeclHead declHead@(H.DHInfix _ _ _) =
  notSupported "Type operators" declHead

-- | Gets the name of a data type or type synonym declaration from the name
--   stored in the head of the declaration.
--
--   The name of the declaration must not be a symbol because type operators
--   are not supported.
simplifyDeclName :: H.Name SrcSpan -> Reporter HS.DeclIdent
simplifyDeclName (H.Ident srcSpan ident) = return (HS.DeclIdent srcSpan ident)
simplifyDeclName sym@(H.Symbol _ _) = notSupported "Type operators" sym

-- | Gets the name of the type variable bound by the given binder.
--
--   The type variable must not be a symbol and the binder must not have
--   an explicit kind annotation.
simplifyTypeVarBind :: H.TyVarBind SrcSpan -> Reporter HS.TypeVarDecl
simplifyTypeVarBind (H.UnkindedVar srcSpan (H.Ident _ ident)) =
  return (HS.DeclIdent srcSpan ident)
simplifyTypeVarBind typeVarBind@(H.UnkindedVar _ (H.Symbol _ _)) =
  notSupported "Type operators" typeVarBind
simplifyTypeVarBind typeVarBind@(H.KindedVar _ _ _) =
  notSupported "Kind annotations" typeVarBind

-------------------------------------------------------------------------------
-- Data type constructor declarations                                        --
-------------------------------------------------------------------------------

-- | Simplifies a constructor declaration of a data type declaration with
--   optional existential quantification binding. Existential quantification
--   bindings are not supported.
simplifyConDecl :: H.QualConDecl SrcSpan -> Reporter HS.ConDecl
simplifyConDecl (H.QualConDecl _ Nothing Nothing conDecl) =
  simplifyConDecl' conDecl
simplifyConDecl conDecl@(H.QualConDecl _ (Just _) _ _) =
  notSupported "Existential quantifications" conDecl
simplifyConDecl conDecl@(H.QualConDecl _ _ (Just _) _) =
  notSupported "Type classes" conDecl

-- | Simplifies a constructor declaration of a data type declaration.
--
--   The constructor must be an ordinary data constructor. Infix constructors
--   @t1 `C` t2@ are treated as syntactic sugar for @C t1 t2@.
--   Record constructors and constructors whose name is a symbol (see
--   'simplifyConDeclName') are not supported.
simplifyConDecl' :: H.ConDecl SrcSpan -> Reporter HS.ConDecl
simplifyConDecl' (H.ConDecl srcSpan conName args) = do
  conIdent <- simplifyConDeclName conName
  args'    <- mapM simplifyType args
  return (HS.ConDecl srcSpan conIdent args')
simplifyConDecl' (H.InfixConDecl pos t1 conName t2) =
  simplifyConDecl' (H.ConDecl pos conName [t1, t2])
simplifyConDecl' conDecl@(H.RecDecl _ _ _) =
  notSupported "Record constructors" conDecl

-- | Gets the name of a constructor declaration.
--
--   The name of the declaration must not be a symbol because custom
--   constructor operators are not supported.
simplifyConDeclName :: H.Name SrcSpan -> Reporter HS.DeclIdent
simplifyConDeclName (H.Ident srcSpan ident) =
  return (HS.DeclIdent srcSpan ident)
simplifyConDeclName sym@(H.Symbol _ _) =
  notSupported "Constructor operator declarations" sym

-------------------------------------------------------------------------------
-- Function declarations                                        --
-------------------------------------------------------------------------------

-- | Simplifies the single rule of a function declaration.
simplifyFuncDecl :: H.Match SrcSpan -> Reporter HS.Decl
simplifyFuncDecl (H.Match srcSpan declName args (H.UnGuardedRhs _ expr) Nothing)
  = do
    declIdent <- simplifyFuncDeclName declName
    args'     <- mapM simplifyVarPat args
    expr'     <- simplifyExpr expr
    return (HS.FuncDecl srcSpan declIdent args' expr')

-- Function declarations with guards and where blocks are not supported.
simplifyFuncDecl (H.Match _ _ _ rhss@(H.GuardedRhss _ _) _) =
  notSupported "Guards" rhss
simplifyFuncDecl (H.Match _ _ _ _ (Just binds)) =
  notSupported "Local declarations" binds

-- Infix function declarations are allowed when they have the for @x `f` y = e@
-- but not @x (...) y = e@ (See 'simplifyFuncDeclName').
--
-- We treat @x1 `f` x2 ... xn@ as syntactic sugar for @f x1 x2 ... xn@.
simplifyFuncDecl (H.InfixMatch pos arg declName args rhs binds) =
  simplifyFuncDecl (H.Match pos declName (arg : args) rhs binds)

-- | Gets the name of a function declaration.
--
--   The name of the declaration must not be a symbol because custom operator
--   declarations are not supported.
simplifyFuncDeclName :: H.Name SrcSpan -> Reporter HS.DeclIdent
simplifyFuncDeclName (H.Ident srcSpan ident) =
  return (HS.DeclIdent srcSpan ident)
simplifyFuncDeclName sym@(H.Symbol _ _) =
  notSupported "Operator declarations" sym

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------

-- | Simplifies the a type expression.
simplifyType :: H.Type SrcSpan -> Reporter HS.Type

-- Function type @'t1' -> 't2'@.
simplifyType (H.TyFun srcSpan t1 t2) = do
  t1' <- simplifyType t1
  t2' <- simplifyType t2
  return (HS.TypeFunc srcSpan t1' t2')

-- Pair type @('t1', 't2')@.
simplifyType (H.TyTuple srcSpan H.Boxed [t1, t2]) = do
  t1' <- simplifyType t1
  t2' <- simplifyType t2
  return (HS.typeApp srcSpan HS.pairTypeConName [t1', t2'])

-- List type @['t']@.
simplifyType (H.TyList srcSpan t) = do
  t' <- simplifyType t
  return (HS.typeApp srcSpan HS.listTypeConName [t'])

-- Type constructor application @'t1' 't2'@.
simplifyType (H.TyApp srcSpan t1 t2) = do
  t1' <- simplifyType t1
  t2' <- simplifyType t2
  return (HS.TypeApp srcSpan t1' t2')

-- Type variable @'ident'@.
simplifyType (H.TyVar srcSpan (H.Ident _ ident)) =
  return (HS.TypeVar srcSpan ident)

-- Type constructor @'ident'@.
simplifyType (H.TyCon srcSpan name) = do
  name' <- simplifyTypeConName name
  return (HS.TypeCon srcSpan name')

-- Type wrapped in parentheses @('t')@.
simplifyType (H.TyParen _ t) = simplifyType t

-- Not supported types.
simplifyType ty@(H.TyForall _ _ _ _) =
  notSupported "Explicit type variable quantifications" ty
simplifyType ty@(H.TyTuple _ H.Unboxed _) = notSupported "Unboxed tuples" ty
simplifyType ty@(H.TyTuple _ H.Boxed _) =
  notSupported "Tuples other than unit and pairs" ty
simplifyType ty@(H.TyUnboxedSum _ _) = notSupported "Unboxed sums" ty
simplifyType ty@(H.TyParArray   _ _) = notSupported "Parallel arrays" ty
simplifyType ty@(H.TyKind _ _ _) =
  notSupported "Types with explicit kind signatures" ty
simplifyType ty@(H.TyVar _ (H.Symbol _ _)) = notSupported "Type operators" ty
simplifyType ty@(H.TyPromoted _ _) = notSupported "Type operators" ty
simplifyType ty@(H.TyInfix _ _ _ _) = notSupported "Type operators" ty
simplifyType ty@(H.TyEquals _ _ _) = notSupported "Type equality predicates" ty
simplifyType ty@(H.TySplice _ _) = notSupported "Template Haskell" ty
simplifyType ty@(H.TyBang _ _ _ _) = notSupported "Striktness annotations" ty
simplifyType ty@(H.TyWildCard _ _) = notSupported "Type wildcards" ty
simplifyType ty@(H.TyQuasiQuote _ _ _) = notSupported "Quasiquotation types" ty

-- | Simplifies the name of a build-in or user defined type constructor.
simplifyTypeConName :: H.QName SrcSpan -> Reporter HS.TypeConName
simplifyTypeConName (H.UnQual  _ (H.Ident _ ident)) = return (HS.Ident ident)
simplifyTypeConName (H.Special _ (H.UnitCon _    )) = return HS.unitTypeConName
simplifyTypeConName (H.Special _ (H.ListCon _    )) = return HS.listTypeConName
simplifyTypeConName name@(H.Special _ (H.TupleCon _ H.Boxed n))
  | n == 2    = return HS.pairTypeConName
  | otherwise = notSupported "Tuples other than unit and pairs" name

-- Not supported type constructor names.
simplifyTypeConName name@(H.UnQual _ (H.Symbol _ _)) =
  notSupported "Type operators" name
simplifyTypeConName name@(H.Qual _ _ _) =
  notSupported "Qualified identifiers" name
simplifyTypeConName name@(H.Special _ (H.FunCon _)) =
  notSupported "Function type constructors" name
simplifyTypeConName name@(H.Special _ (H.TupleCon _ H.Unboxed _)) =
  notSupported "Unboxed tuples" name
simplifyTypeConName name@(H.Special _ (H.UnboxedSingleCon _)) =
  notSupported "Unboxed tuples" name
simplifyTypeConName name@(H.Special _ (H.ExprHole _)) =
  notSupported "Expression holes" name
simplifyTypeConName name@(H.Special _ (H.Cons _)) = usageError
  "The data constructor (:) cannot be used as a type constructor!"
  name

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Simplifies an expression.
simplifyExpr :: H.Exp SrcSpan -> Reporter HS.Expr

-- Error terms are regular functions but need to be handled differently.
simplifyExpr (H.Var srcSpan (H.UnQual _ (H.Ident _ "undefined"))) =
  return (HS.Undefined srcSpan)
simplifyExpr (H.App srcSpan (H.Var _ (H.UnQual _ (H.Ident _ "error"))) arg) =
  case arg of
    (H.Lit _ (H.String _ msg _)) -> return (HS.ErrorExpr srcSpan msg)
    _ -> notSupported "Non-literal error messages" arg
simplifyExpr expr@(H.Var _ (H.UnQual _ (H.Ident _ "error"))) =
  usageError "The function 'error' must be applied immediately." expr

-- Parenthesis.
simplifyExpr (H.Paren _       expr) = simplifyExpr expr

-- Variables.
simplifyExpr (H.Var   srcSpan name) = do
  name' <- simplifyVarName name
  return (HS.Var srcSpan name')

-- Constructors.
simplifyExpr (H.Con srcSpan name) = do
  name' <- simplifyConName name
  return (HS.Con srcSpan name')

-- Integer literals.
simplifyExpr (H.Lit srcSpan (H.Int _ value _)) =
  return (HS.IntLiteral srcSpan value)

-- Pairs.
simplifyExpr (H.Tuple srcSpan H.Boxed [e1, e2]) = do
  e1' <- simplifyExpr e1
  e2' <- simplifyExpr e2
  return (HS.conApp srcSpan HS.pairConName [e1', e2'])

-- List literals are converted to a chain of 'HS.consConName' applications
-- with a trailing 'HS.nilConName'. All generated constructors refer to
-- the same source span of the original list literal.
simplifyExpr (H.List srcSpan exprs) = do
  let nil  = HS.Con srcSpan HS.nilConName
      cons = HS.Con srcSpan HS.consConName
  exprs' <- mapM simplifyExpr exprs
  return (foldr (HS.App srcSpan . HS.App srcSpan cons) nil exprs')

-- Function applications.
simplifyExpr (H.App srcSpan e1 e2) = do
  e1' <- simplifyExpr e1
  e2' <- simplifyExpr e2
  return (HS.App srcSpan e1' e2')

-- Infix operator, function or constructor applications.
simplifyExpr (H.InfixApp srcSpan e1 op e2) = do
  e1' <- simplifyExpr e1
  op' <- simplifyOp op
  e2' <- simplifyExpr e2
  return (HS.InfixApp srcSpan e1' op' e2')

-- Partial infix applications.
simplifyExpr (H.LeftSection srcSpan e1 op) = do
  e1' <- simplifyExpr e1
  op' <- simplifyOp op
  return (HS.LeftSection srcSpan e1' op')
simplifyExpr (H.RightSection srcSpan op e2) = do
  op' <- simplifyOp op
  e2' <- simplifyExpr e2
  return (HS.RightSection srcSpan op' e2')

-- Negation.
simplifyExpr (H.NegApp srcSpan e) = do
  e' <- simplifyExpr e
  return (HS.NegApp srcSpan e')

-- Lambda abstractions.
simplifyExpr (H.Lambda srcSpan args expr) = do
  args' <- mapM simplifyVarPat args
  expr' <- simplifyExpr expr
  return (HS.Lambda srcSpan args' expr')

-- Conditional expressions.
simplifyExpr (H.If srcSpan e1 e2 e3) = do
  e1' <- simplifyExpr e1
  e2' <- simplifyExpr e2
  e3' <- simplifyExpr e3
  return (HS.If srcSpan e1' e2' e3')

-- Case expressions.
simplifyExpr (H.Case srcSpan expr alts) = do
  expr' <- simplifyExpr expr
  alts' <- mapM simplifyAlt alts
  return (HS.Case srcSpan expr' alts')

-- Not supported expressions.
simplifyExpr expr@(H.OverloadedLabel _ _) =
  notSupported "Overloaded labels" expr
simplifyExpr expr@(H.IPVar _ _) =
  notSupported "Implicit parameter variables" expr
simplifyExpr expr@(H.Let _ _ _) = notSupported "Local declarations" expr
simplifyExpr expr@(H.MultiIf _ _) =
  notSupported "Multi-Way if expressions" expr
simplifyExpr expr@(H.Do  _ _            ) = notSupported "do-expressions" expr
simplifyExpr expr@(H.MDo _ _            ) = notSupported "mdo-expressions" expr
simplifyExpr expr@(H.Tuple _ H.Unboxed _) = notSupported "Unboxed tuples" expr
simplifyExpr expr@(H.Tuple _ H.Boxed _) =
  notSupported "Tuples other than unit and pairs" expr
simplifyExpr expr@(H.UnboxedSum _ _ _ _) = notSupported "Unboxed sums" expr
simplifyExpr expr@(H.TupleSection _ _ _) = notSupported "Tuple sections" expr
simplifyExpr expr@(H.ParArray _ _) = notSupported "Parallel arrays" expr
simplifyExpr expr@(H.RecConstr _ _ _) = notSupported "Record constructors" expr
simplifyExpr expr@(H.RecUpdate _ _ _) = notSupported "Record updates" expr
simplifyExpr expr@(H.EnumFrom _ _) = notSupported "Enumerations" expr
simplifyExpr expr@(H.EnumFromTo _ _ _) = notSupported "Enumerations" expr
simplifyExpr expr@(H.EnumFromThen _ _ _) = notSupported "Enumerations" expr
simplifyExpr expr@(H.EnumFromThenTo _ _ _ _) = notSupported "Enumerations" expr
simplifyExpr expr@(H.ParArrayFromTo _ _ _) =
  notSupported "Parallel arrays" expr
simplifyExpr expr@(H.ParArrayFromThenTo _ _ _ _) =
  notSupported "Parallel arrays" expr
simplifyExpr expr@(H.ListComp _ _ _) = notSupported "List comprehensions" expr
simplifyExpr expr@(H.ParComp _ _ _) =
  notSupported "Parallel list comprehensions" expr
simplifyExpr expr@(H.ParArrayComp _ _ _) =
  notSupported "Parallel array comprehensions" expr
simplifyExpr expr@(H.ExpTypeSig _ _ _) =
  notSupported "Expressions with explicit type signatures" expr
simplifyExpr expr@(H.VarQuote   _ _  ) = notSupported "Template Haskell" expr
simplifyExpr expr@(H.TypQuote   _ _  ) = notSupported "Template Haskell" expr
simplifyExpr expr@(H.BracketExp _ _  ) = notSupported "Template Haskell" expr
simplifyExpr expr@(H.SpliceExp  _ _  ) = notSupported "Template Haskell" expr
simplifyExpr expr@(H.QuasiQuote _ _ _) = notSupported "Quasiquotation" expr
simplifyExpr expr@(H.TypeApp _ _) =
  notSupported "Visible type applications" expr
simplifyExpr expr@(H.XTag _ _ _ _ _     ) = notSupported "XML elements" expr
simplifyExpr expr@(H.XETag _ _ _ _      ) = notSupported "XML elements" expr
simplifyExpr expr@(H.XPcdata   _ _      ) = notSupported "XML elements" expr
simplifyExpr expr@(H.XExpTag   _ _      ) = notSupported "XML elements" expr
simplifyExpr expr@(H.XChildTag _ _      ) = notSupported "XML elements" expr
simplifyExpr expr@(H.CorePragma _ _ _   ) = notSupported "Pragmas" expr
simplifyExpr expr@(H.SCCPragma  _ _ _   ) = notSupported "Pragmas" expr
simplifyExpr expr@(H.GenPragma _ _ _ _ _) = notSupported "Pragmas" expr
simplifyExpr expr@(H.Proc _ _ _) = notSupported "Arrow expressions" expr
simplifyExpr expr@(H.LeftArrApp _ _ _) = notSupported "Arrow expressions" expr
simplifyExpr expr@(H.RightArrApp _ _ _) = notSupported "Arrow expressions" expr
simplifyExpr expr@(H.LeftArrHighApp _ _ _) =
  notSupported "Arrow expressions" expr
simplifyExpr expr@(H.RightArrHighApp _ _ _) =
  notSupported "Arrow expressions" expr
simplifyExpr expr@(H.LCase _ _) = notSupported "Lambda case expressions" expr

-- Not supported literals.
simplifyExpr expr@(H.Lit _ (H.Char _ _ _)) =
  notSupported "Character literals" expr
simplifyExpr expr@(H.Lit _ (H.String _ _ _)) =
  notSupported "String literals" expr
simplifyExpr expr@(H.Lit _ (H.Frac _ _ _)) =
  notSupported "Floating point literals" expr
simplifyExpr expr@(H.Lit _ (H.PrimInt _ _ _)) =
  notSupported "Unboxed integer literals" expr
simplifyExpr expr@(H.Lit _ (H.PrimWord _ _ _)) =
  notSupported "Unboxed word literals" expr
simplifyExpr expr@(H.Lit _ (H.PrimFloat _ _ _)) =
  notSupported "Unboxed float literals" expr
simplifyExpr expr@(H.Lit _ (H.PrimDouble _ _ _)) =
  notSupported "Unboxed double literals" expr
simplifyExpr expr@(H.Lit _ (H.PrimChar _ _ _)) =
  notSupported "Unboxed character literals" expr
simplifyExpr expr@(H.Lit _ (H.PrimString _ _ _)) =
  notSupported "Unboxed string literals" expr

-- | Simplifies an infix operator.
simplifyOp :: H.QOp SrcSpan -> Reporter HS.Op
simplifyOp (H.QVarOp srcSpan name) =
  simplifyVarName name >>= return . HS.VarOp srcSpan
simplifyOp (H.QConOp srcSpan name) =
  simplifyConName name >>= return . HS.ConOp srcSpan

-- | Gets the name of a variable, defined function or predefined function (e.g.
--   @(+)@).
simplifyVarName :: H.QName SrcSpan -> Reporter HS.VarName
simplifyVarName (H.UnQual _ (H.Ident _ ident)) = return (HS.Ident ident)
simplifyVarName (H.UnQual _ (H.Symbol _ sym)) = return (HS.Symbol sym)
simplifyVarName name@(H.Qual _ _ _) = notSupported "Qualified identifiers" name
simplifyVarName name@(H.Special _ _) =
  usageError "Constructors cannot be used as variables!" name

-- | Gets the name of a build-in or user defined constructor.
simplifyConName :: H.QName SrcSpan -> Reporter HS.ConName
simplifyConName (H.UnQual  _ (H.Ident _ ident)) = return (HS.Ident ident)
simplifyConName (H.Special _ (H.UnitCon _    )) = return HS.unitConName
simplifyConName (H.Special _ (H.ListCon _    )) = return HS.nilConName
simplifyConName (H.Special _ (H.Cons    _    )) = return HS.consConName
simplifyConName name@(H.Special _ (H.TupleCon _ H.Boxed n))
  | n == 2    = return HS.pairConName
  | otherwise = notSupported "Tuples other than unit and pairs" name

-- Not supported constructor names.
simplifyConName name@(H.Qual _ _ _) = notSupported "Qualified identifiers" name
simplifyConName name@(H.UnQual _ (H.Symbol _ _)) =
  notSupported "User defined data constructor operatos" name
simplifyConName name@(H.Special _ (H.FunCon _)) =
  usageError "Function type constructor cannot be used as a constructor!" name
simplifyConName name@(H.Special _ (H.TupleCon _ H.Unboxed _)) =
  notSupported "Unboxed tuples" name
simplifyConName name@(H.Special _ (H.UnboxedSingleCon _)) =
  notSupported "Unboxed tuples" name
simplifyConName name@(H.Special _ (H.ExprHole _)) =
  notSupported "Expression holes" name

-- | Simplifies a variable pattern (e.g. the parameters of a lambda abstraction
--   or function declaration).
--
--  Parenthesis are ignored.
simplifyVarPat :: H.Pat SrcSpan -> Reporter HS.VarPat
simplifyVarPat (H.PVar srcSpan (H.Ident _ ident)) =
  return (HS.VarPat srcSpan ident)
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
simplifyConPat :: H.Pat SrcSpan -> Reporter (HS.ConPat, [HS.VarPat])

-- Ignore parentheses.
simplifyConPat (H.PParen _ pat    ) = simplifyConPat pat

-- Regular constructor pattern.
simplifyConPat (H.PApp _ name args) = do
  name' <- simplifyConName name
  vars  <- mapM simplifyVarPat args
  return (HS.ConPat (H.ann name) name', vars)

-- Infix constructor pattern (e.g. @x : xs@).
simplifyConPat (H.PInfixApp _ p1 name p2) = do
  v1    <- simplifyVarPat p1
  name' <- simplifyConName name
  v2    <- simplifyVarPat p2
  return (HS.ConPat (H.ann name) name', [v1, v2])

-- Pair constructor pattern.
simplifyConPat (H.PTuple srcSpan H.Boxed [p1, p2]) = do
  v1 <- simplifyVarPat p1
  v2 <- simplifyVarPat p2
  return (HS.ConPat srcSpan HS.pairConName, [v1, v2])

-- Other tuple constructor patterns are not supported.
simplifyConPat pat@(H.PTuple _ H.Unboxed _) = notSupported "Unboxed tuples" pat
simplifyConPat pat@(H.PTuple _ H.Boxed _) =
  notSupported "Tuples other than unit and pairs" pat

-- The list notation pattern @[x1, ..., xn]@ is not supported because it is
-- not a shallow pattern (i.e. cannot be represented as a pair of constructor
-- name and variable patterns).
-- But we allow the empty list pattern @[]@.
simplifyConPat (H.PList srcSpan []) =
  return (HS.ConPat srcSpan HS.nilConName, [])
simplifyConPat pat@(H.PList _ _ ) = notSupported "List notation patterns" pat

-- Record constructors are not supported.
simplifyConPat pat@(H.PRec _ _ _) = notSupported "Record constructors" pat

-- All other non-constructor patterns are not supported (e.g. variable,
-- wildcard or as-patterns etc.).
simplifyConPat pat                = expected "constructor pattern" pat

-- | Simplifies an alternative of a case expression.
simplifyAlt :: H.Alt SrcSpan -> Reporter HS.Alt
simplifyAlt (H.Alt srcSpan pat (H.UnGuardedRhs _ expr) Nothing) = do
  (con, vars) <- simplifyConPat pat
  expr'       <- simplifyExpr expr
  return (HS.Alt srcSpan con vars expr')
simplifyAlt (H.Alt _ _ rhss@(H.GuardedRhss _ _) _) = notSupported "Guards" rhss
simplifyAlt (H.Alt _ _ _ (Just binds)) =
  notSupported "Local declarations" binds
