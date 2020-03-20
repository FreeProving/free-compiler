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

import qualified Data.Foldable                 as OSet
                                                ( toList )
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set
import           Data.Set.Ordered               ( OSet
                                                , (\\)
                                                )
import qualified Data.Set.Ordered              as OSet

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
varName :: HS.QName -> OSet DependencyName
varName = OSet.singleton . VarName

-- | Smart constructor for a set that contains the name of a single (type)
--   constructor dependency.
conName :: HS.QName -> OSet DependencyName
conName = OSet.singleton . ConName

-- | Gets the 'HS.Name' wrapped by the given dependency name.
unwrap :: DependencyName -> HS.QName
unwrap (VarName name) = name
unwrap (ConName name) = name

-- | Gets a list of all 'HS.Names' wrapped by dependency names in the
--   given set.
unwrapSet :: OSet DependencyName -> [HS.QName]
unwrapSet = map unwrap . OSet.toList

-- | Tests whether the given name is the name of a (type) variable dependency.
isVarName :: DependencyName -> Bool
isVarName (VarName _) = True
isVarName (ConName _) = False

-- | Tests whether the given name is the name of a (type) constructor
--   dependency.
isConName :: DependencyName -> Bool
isConName (VarName _) = True
isConName (ConName _) = False

-- | Inserts an element before all elements in the given set.
--
--   If the set contains the element already, the new index takes precedence.
insertBefore :: Ord a => a -> OSet a -> OSet a
insertBefore = (OSet.|<)

-- | When calculating the union of two ordered sets and an element is a
--   member of both sets, the indices of the first set take precedence.
union :: Ord a => OSet a -> OSet a -> OSet a
union = (OSet.|<>)

-- | Calculates the union of the given set using 'union'.
unions :: Ord a => [OSet a] -> OSet a
unions = foldr union OSet.empty

-------------------------------------------------------------------------------
-- Types                                                                     --
-------------------------------------------------------------------------------

-- | Type class for AST nodes that can depend on types.
class TypeDependencies a where
  -- | Extracts the names of all type variables and type constructors used
  --   by the given AST node and remembers for every name whether it is
  --   the name of a type variable or type constructor.
  typeDependencies' :: a -> OSet DependencyName

-- | Utility instance to get the type dependencies of an optional value.
instance TypeDependencies a => TypeDependencies (Maybe a) where
  typeDependencies' = maybe OSet.empty typeDependencies'

-- | Utility instance to get the type dependencies of all elements in a list.
instance TypeDependencies a => TypeDependencies [a] where
  typeDependencies' = unions . map typeDependencies'

-- | Type expressions can depend on types.
instance TypeDependencies HS.Type where
  typeDependencies' (HS.TypeVar _ ident) = varName (HS.UnQual (HS.Ident ident))
  typeDependencies' (HS.TypeCon _ name ) = conName name
  typeDependencies' (HS.TypeApp _ t1 t2) =
    typeDependencies' t1 `union` typeDependencies' t2
  typeDependencies' (HS.FuncType _ t1 t2) =
    typeDependencies' t1 `union` typeDependencies' t2

-- | A type schema depends on the types it's type expression depends on
--   but not on the type variables bound by the type schema.
instance TypeDependencies HS.TypeSchema where
  typeDependencies' (HS.TypeSchema _ typeArgs typeExpr) =
    withoutTypeArgs typeArgs (typeDependencies' typeExpr)

-- | An expression depends on the types used in explicit type applications
--   and type signatures.
instance TypeDependencies HS.Expr where
  typeDependencies' (HS.Con _ _ exprType) = typeDependencies' exprType
  typeDependencies' (HS.Var _ _ exprType) = typeDependencies' exprType
  typeDependencies' (HS.App _ e1 e2 exprType) =
    typeDependencies' [e1, e2] `union` typeDependencies' exprType
  typeDependencies' (HS.TypeAppExpr _ expr typeExpr exprType) =
    typeDependencies' expr
      `union` typeDependencies' typeExpr
      `union` typeDependencies' exprType
  typeDependencies' (HS.If _ e1 e2 e3 exprType) =
    typeDependencies' [e1, e2, e3]
      `union` typeDependencies' exprType
  typeDependencies' (HS.Case _ expr alts exprType) =
    typeDependencies' expr
      `union` typeDependencies' alts
      `union` typeDependencies' exprType
  typeDependencies' (HS.Undefined _ exprType   ) = typeDependencies' exprType
  typeDependencies' (HS.ErrorExpr  _ _ exprType) = typeDependencies' exprType
  typeDependencies' (HS.IntLiteral _ _ exprType) = typeDependencies' exprType
  typeDependencies' (HS.Lambda _ args expr exprType) =
    typeDependencies' args
      `union` typeDependencies' expr
      `union` typeDependencies' exprType

-- | An alternative of a @case@ expression depends on the types it's
--   right-hand side depends on.
instance TypeDependencies HS.Alt where
  typeDependencies' (HS.Alt _ _ varPats expr) =
    typeDependencies' varPats `union` typeDependencies' expr

-- | A function declaration depends on the types it's right-hand side
--   depends on.
instance TypeDependencies HS.FuncDecl where
  typeDependencies' (HS.FuncDecl _ _ typeArgs args rhs maybeRetType) =
    withoutTypeArgs typeArgs
      $       typeDependencies' args
      `union` typeDependencies' args
      `union` typeDependencies' rhs
      `union` typeDependencies' maybeRetType

-- | A variable pattern depends on the types it's annotated type depends on.
instance TypeDependencies HS.VarPat where
  typeDependencies' (HS.VarPat _ _ maybeVarType) =
    typeDependencies' maybeVarType

-- | Extracts the names of all type variables and type constructors used in
--   the given type expression.
--
--   This also includes the names of predefied constructors.
typeDependencies :: TypeDependencies a => a -> [HS.QName]
typeDependencies = unwrapSet . typeDependencies'

-- | Extracts the names of all type variables used in the given type
--   expression.
typeVars :: TypeDependencies a => a -> [HS.QName]
typeVars = map unwrap . filter isVarName . OSet.toList . typeDependencies'

-- | Like 'typeVars' but returns a set of variable names.
typeVarSet :: TypeDependencies a => a -> Set HS.QName
typeVarSet =
  Set.map unwrap . Set.filter isVarName . OSet.toSet . typeDependencies'

-- | Extracts the names of all type constructors used in the given type
--   expression.
--
--   This also includes the names of predefined constructors (e.g. the list
--   and pair constructors).
typeCons :: TypeDependencies a => a -> [HS.QName]
typeCons = unwrapSet . OSet.filter isConName . typeDependencies'

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
varSet = Set.map unwrap . Set.filter isVarName . OSet.toSet . exprDependencies'

-- | Extracts the names of all constructors used in the given expression.
--
--   This also includes predefined constructors.
cons :: HS.Expr -> [HS.QName]
cons = unwrapSet . OSet.filter isConName . exprDependencies'

-- | Extracts the names of all variables, functions and constructors used in
--   the given expression and remembers for every name whether it is the name
--   of a variable (or function) or constructor.
exprDependencies' :: HS.Expr -> OSet DependencyName
exprDependencies' (HS.Var _ name _) = varName name
exprDependencies' (HS.Con _ name _) = conName name
exprDependencies' (HS.App _ e1 e2 _) =
  exprDependencies' e1 `union` exprDependencies' e2
exprDependencies' (HS.TypeAppExpr _ expr _ _) = exprDependencies' expr
exprDependencies' (HS.If _ e1 e2 e3 _) =
  unions (map exprDependencies' [e1, e2, e3])
exprDependencies' (HS.Case _ expr alts _) =
  unions (exprDependencies' expr : map altDependencies alts)
exprDependencies' (HS.Undefined _ _   ) = varName HS.undefinedFuncName
exprDependencies' (HS.ErrorExpr  _ _ _) = conName HS.errorFuncName
exprDependencies' (HS.IntLiteral _ _ _) = OSet.empty
exprDependencies' (HS.Lambda _ args expr _) =
  withoutArgs args (exprDependencies' expr)

-- | Extracts the names of all variables, functions and constructors used in
--   the given alternative of a @case@-expression.
altDependencies :: HS.Alt -> OSet DependencyName
altDependencies (HS.Alt _ (HS.ConPat _ name) args expr) =
  ConName name `insertBefore` withoutArgs args (exprDependencies' expr)

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
typeDeclDependencies = map unwrap . OSet.toList . typeDeclDependencies'

-- | Like 'typeDeclDependencies' but returns the type's dependencies
--   as a 'Set'.
typeDeclDependencySet :: HS.TypeDecl -> Set HS.QName
typeDeclDependencySet = Set.map unwrap . OSet.toSet . typeDeclDependencies'

-- | Extracts the dependencies of the given data type or type synonym
--   declaration on type constructors (and undeclared type variables) and
--   remebers for every name whether it is the name of a type variable or
--   of a type constructor.
typeDeclDependencies' :: HS.TypeDecl -> OSet DependencyName
typeDeclDependencies' (HS.TypeSynDecl _ _ typeArgs typeExpr) =
  withoutTypeArgs typeArgs (typeDependencies' typeExpr)
typeDeclDependencies' (HS.DataDecl _ _ typeArgs conDecls) =
  withoutTypeArgs typeArgs (unions (map conDeclDependencies conDecls))

-- | Extracts the dependencies of the field types of the given constructor
--   declaration.
conDeclDependencies :: HS.ConDecl -> OSet DependencyName
conDeclDependencies (HS.ConDecl _ _ types) =
  unions (map typeDependencies' types)

-- | Removes the names of the given type variable declarations from a set
--   of dependency names.
withoutTypeArgs
  :: [HS.TypeVarDecl] -> OSet DependencyName -> OSet DependencyName
withoutTypeArgs args set =
  set \\ OSet.fromList (map (VarName . HS.typeVarDeclQName) args)

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
funcDeclDependencySet = Set.map unwrap . OSet.toSet . funcDeclDependencySet'

-- | Extracts the dependencies of the given function declaration on
--   constructors and other functions and remembers for every name whether it
--   is the name of a function or constructor.
funcDeclDependencySet' :: HS.FuncDecl -> OSet DependencyName
funcDeclDependencySet' (HS.FuncDecl _ _ _ args expr _) =
  withoutArgs args (exprDependencies' expr)

-- | Removes the names for the given variable patterns from a set of
--   dependencies.
withoutArgs :: [HS.VarPat] -> OSet DependencyName -> OSet DependencyName
withoutArgs args set =
  set \\ OSet.fromList (map (VarName . HS.varPatQName) args)

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
