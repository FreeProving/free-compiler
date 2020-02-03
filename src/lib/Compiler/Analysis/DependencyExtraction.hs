-- | This module contains functions to extract the names of (type) constructors
--   and variables (including functions) used by a Haskell type, expression or
--   declaration.
--
--   These functions are used by "Compiler.Analysis.DependencyGraph" to
--   construct the dependency graph. They are also used during the conversion
--   of function declarations to extract the type variables used in the type
--   signature (becuase in Coq we need to declare type variables explicitly).

module Compiler.Analysis.DependencyExtraction
  ( -- * Types
    typeDependencies
  , typeVars
  , typeVarSet
  , typeCons
    -- * Expressions
  , exprDependencies
  , vars
  , varSet
  , cons
    -- * Type declarations
  , typeDeclDependencies
  , typeDeclDependencySet
    -- * Function declarations
  , funcDeclDependencies
  , funcDeclDependencySet
    -- * Modules
  , moduleDependencies
  , moduleDependencySet
  )
where

import           Data.Set                       ( Set
                                                , (\\)
                                                )
import qualified Data.Set                      as Set

import qualified Compiler.Haskell.AST          as HS


-------------------------------------------------------------------------------
-- Common utilities                                                          --
-------------------------------------------------------------------------------

-- | Wrapper that is used by 'typeDependencies'' and 'exprDependencies'' to
--   remember whether a name is a variable or constructor name such that
--   'typeVars', 'typeCons', 'vars' and 'cons' can filter them appropriatly.
data DependencyName = VarName HS.QName | ConName HS.QName
  deriving (Eq, Ord, Show)

-- | Smart constructor for a set that contains the name of a single (type)
--   variable dependency.
varName :: HS.QName -> Set DependencyName
varName = Set.singleton . VarName

-- | Smart constructor for a set that contains the name of a single (type)
--   constructor dependency.
conName :: HS.QName -> Set DependencyName
conName = Set.singleton . ConName

-- | Gets the 'HS.Name' wrapped by the given dependency name.
unwrap :: DependencyName -> HS.QName
unwrap (VarName name) = name
unwrap (ConName name) = name

-- | Gets a list of all 'HS.Names' wrapped by dependency names in the
--   given set.
unwrapSet :: Set DependencyName -> [HS.QName]
unwrapSet = Set.toList . Set.map unwrap

-- | Tests whether the given name is the name of a (type) variable dependency.
isVarName :: DependencyName -> Bool
isVarName (VarName _) = True
isVarName (ConName _) = False

-- | Tests whether the given name is the name of a (type) constructor
--   dependency.
isConName :: DependencyName -> Bool
isConName (VarName _) = True
isConName (ConName _) = False

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------

-- | Type class for AST nodes that can depend on types.
class TypeDependencies a where
  -- | Extracts the names of all type variables and type constructors used
  --   by the given AST node and remembers for every name whether it is
  --   the name of a type variable or type constructor.
  typeDependencies' :: a -> Set DependencyName

-- | Type expressions can depend on types.
instance TypeDependencies HS.Type where
  typeDependencies' (HS.TypeVar _ ident) = varName (HS.UnQual (HS.Ident ident))
  typeDependencies' (HS.TypeCon _ name ) = conName name
  typeDependencies' (HS.TypeApp _ t1 t2) =
    typeDependencies' t1 `Set.union` typeDependencies' t2
  typeDependencies' (HS.TypeFunc _ t1 t2) =
    typeDependencies' t1 `Set.union` typeDependencies' t2

-- | A type schema depends on the types it's type expression depends on
--   but not on the type variables bound by the type schema.
instance TypeDependencies HS.TypeSchema where
  typeDependencies' (HS.TypeSchema _ typeArgs typeExpr) =
    withoutTypeArgs typeArgs (typeDependencies' typeExpr)

-- | An expression depends on the types used in explicit type applications
--   and type signatures.
instance TypeDependencies HS.Expr where
  typeDependencies' (HS.Con _ _) = Set.empty
  typeDependencies' (HS.Var _ _) = Set.empty
  typeDependencies' (HS.App _ e1 e2) =
    typeDependencies' e1 `Set.union` typeDependencies' e2
  typeDependencies' (HS.TypeAppExpr _ expr typeExpr) =
    typeDependencies' expr `Set.union` typeDependencies' typeExpr
  typeDependencies' (HS.If _ e1 e2 e3) =
    Set.unions (map typeDependencies' [e1, e2, e3])
  typeDependencies' (HS.Case _ expr alts) =
    Set.unions (typeDependencies' expr : map typeDependencies' alts)
  typeDependencies' (HS.Undefined _    ) = Set.empty
  typeDependencies' (HS.ErrorExpr  _ _ ) = Set.empty
  typeDependencies' (HS.IntLiteral _ _ ) = Set.empty
  typeDependencies' (HS.Lambda _ _ expr) = typeDependencies' expr
  typeDependencies' (HS.ExprTypeSig _ expr typeSchema) =
    typeDependencies' expr `Set.union` typeDependencies' typeSchema

-- | An alternative of a @case@ expression depends on the types it's
--   right-hand side depends on.
instance TypeDependencies HS.Alt where
  typeDependencies' (HS.Alt _ _ _ expr) = typeDependencies' expr

-- | A function declaration depends on the types it's right-hand side
--   depends on.
instance TypeDependencies HS.FuncDecl where
  typeDependencies' (HS.FuncDecl _ _ _ rhs) = typeDependencies' rhs

-- | Extracts the names of all type variables and type constructors used in
--   the given type expression.
--
--   This also includes the names of predefied constructors.
typeDependencies :: TypeDependencies a => a -> [HS.QName]
typeDependencies = unwrapSet . typeDependencies'

-- | Extracts the names of all type variables used in the given type
--   expression.
typeVars :: TypeDependencies a => a -> [HS.QName]
typeVars = Set.toList . typeVarSet

-- | Like 'typeVars' but returns a set of variable names.
typeVarSet :: TypeDependencies a => a -> Set HS.QName
typeVarSet = Set.map unwrap . Set.filter isVarName . typeDependencies'

-- | Extracts the names of all type constructors used in the given type
--   expression.
--
--   This also includes the names of predefined constructors (e.g. the list
--   and pair constructors).
typeCons :: TypeDependencies a => a -> [HS.QName]
typeCons = unwrapSet . Set.filter isConName . typeDependencies'

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Extracts the names of all variables, functions and constructors used in
--   the given expression.
--
--   This also includes the names of predefined functions, error terms like
--   @undefined@ and @error@ as well as constructors.
exprDependencies :: HS.Expr -> [HS.QName]
exprDependencies = unwrapSet . exprDependencies'

-- | Extracts the names of all variables used in the given expression.
--
--   This also includes the names of functions, predefined functions and the
--   error terms @undefined@ and @error@.
vars :: HS.Expr -> [HS.QName]
vars = Set.toList . varSet

-- | Like 'vars' but returns a set of variable names.
varSet :: HS.Expr -> Set HS.QName
varSet = Set.map unwrap . Set.filter isVarName . exprDependencies'

-- | Extracts the names of all constructors used in the given expression.
--
--   This also includes predefined constructors.
cons :: HS.Expr -> [HS.QName]
cons = unwrapSet . Set.filter isConName . exprDependencies'

-- | Extracts the names of all variables, functions and constructors used in
--   the given expression and remembers for every name whether it is the name
--   of a variable (or function) or constructor.
exprDependencies' :: HS.Expr -> Set DependencyName
exprDependencies' (HS.Var _ name) = varName name
exprDependencies' (HS.Con _ name) = conName name
exprDependencies' (HS.App _ e1 e2) =
  exprDependencies' e1 `Set.union` exprDependencies' e2
exprDependencies' (HS.TypeAppExpr _ expr _) = exprDependencies' expr
exprDependencies' (HS.If _ e1 e2 e3) =
  Set.unions (map exprDependencies' [e1, e2, e3])
exprDependencies' (HS.Case _ expr alts) =
  Set.unions (exprDependencies' expr : map altDependencies alts)
exprDependencies' (HS.Undefined _   ) = varName HS.undefinedFuncName
exprDependencies' (HS.ErrorExpr  _ _) = conName HS.errorFuncName
exprDependencies' (HS.IntLiteral _ _) = Set.empty
exprDependencies' (HS.Lambda _ args expr) =
  withoutArgs args (exprDependencies' expr)
exprDependencies' (HS.ExprTypeSig _ expr _) = exprDependencies' expr

-- | Extracts the names of all variables, functions and constructors used in
--   the given alternative of a @case@-expression.
altDependencies :: HS.Alt -> Set DependencyName
altDependencies (HS.Alt _ (HS.ConPat _ name) args expr) =
  Set.insert (ConName name) (withoutArgs args (exprDependencies' expr))

-------------------------------------------------------------------------------
-- Type declarations                                   --
-------------------------------------------------------------------------------

-- | Extracts the dependencies of the given data type or type synonym
--   declaration on type constructors (if a constructor contains undeclared
--   type variables, the returned set contains the names of those type
--   variables as well).
--
--   Returns an empty set if the given declaration is not a type declaration.
typeDeclDependencies :: HS.TypeDecl -> [HS.QName]
typeDeclDependencies = Set.toList . typeDeclDependencySet

-- | Like 'typeDeclDependencies' but returns the type's dependencies
--   as a 'Set'.
typeDeclDependencySet :: HS.TypeDecl -> Set HS.QName
typeDeclDependencySet = Set.map unwrap . typeDeclDependencies'

-- | Extracts the dependencies of the given data type or type synonym
--   declaration on type constructors (and undeclared type variables) and
--   remebers for every name whether it is the name of a type variable or
--   of a type constructor.
typeDeclDependencies' :: HS.TypeDecl -> Set DependencyName
typeDeclDependencies' (HS.TypeSynDecl _ _ typeArgs typeExpr) =
  withoutTypeArgs typeArgs (typeDependencies' typeExpr)
typeDeclDependencies' (HS.DataDecl _ _ typeArgs conDecls) =
  withoutTypeArgs typeArgs (Set.unions (map conDeclDependencies conDecls))

-- | Extracts the dependencies of the field types of the given constructor
--   declaration.
conDeclDependencies :: HS.ConDecl -> Set DependencyName
conDeclDependencies (HS.ConDecl _ _ types) =
  Set.unions (map typeDependencies' types)

-- | Removes the names of the given type variable declarations from a set
--   of dependency names.
withoutTypeArgs :: [HS.TypeVarDecl] -> Set DependencyName -> Set DependencyName
withoutTypeArgs args set = set \\ Set.fromList
  (map (VarName . HS.UnQual . HS.Ident . HS.fromDeclIdent) args)

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

-- | Extracts the dependencies of the given function declaration on
--   constructors and other functions.
--
--   Returns an empty set if the given declaration is not a function
--   declaration.
funcDeclDependencies :: HS.FuncDecl -> [HS.QName]
funcDeclDependencies = Set.toList . funcDeclDependencySet

-- | Like 'funcDeclDependencies' but returns the function's dependencies
--   as a 'Set'.
funcDeclDependencySet :: HS.FuncDecl -> Set HS.QName
funcDeclDependencySet = Set.map unwrap . funcDeclDependencySet'

-- | Extracts the dependencies of the given function declaration on
--   constructors and other functions and remembers for every name whether it
--   is the name of a function or constructor.
funcDeclDependencySet' :: HS.FuncDecl -> Set DependencyName
funcDeclDependencySet' (HS.FuncDecl _ _ args expr) =
  withoutArgs args (exprDependencies' expr)

-- | Removes the names for the given variable patterns from a set of
--   dependencies.
withoutArgs :: [HS.VarPat] -> Set DependencyName -> Set DependencyName
withoutArgs args set = set
  \\ Set.fromList (map (VarName . HS.UnQual . HS.Ident . HS.fromVarPat) args)

-------------------------------------------------------------------------------
-- Modules                                                                   --
-------------------------------------------------------------------------------

-- | Extracts the dependencies of the given module on other modules.
--
--   Every module depends on the @Prelude@ module implicitly.
moduleDependencies :: HS.Module -> [HS.ModName]
moduleDependencies =
  Set.toList . Set.insert HS.preludeModuleName . moduleDependencySet

-- | Like 'moduleDependencies' but returnes a set of imported modules.
moduleDependencySet :: HS.Module -> Set HS.ModName
moduleDependencySet = Set.fromList . map HS.importName . HS.modImports
