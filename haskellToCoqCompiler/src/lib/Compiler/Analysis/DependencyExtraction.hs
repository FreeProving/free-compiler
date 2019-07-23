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
  , typeCons
    -- * Expressions
  , exprDependencies
  , vars
  , cons
    -- * Type declarations
  , typeDeclDependencies
    -- * Function declarations
  , funcDeclDependencies
  )
where

import           Data.Set                       ( Set
                                                , (\\)
                                                )
import qualified Data.Set                      as Set

import qualified Compiler.Language.Haskell.SimpleAST
                                               as HS


-------------------------------------------------------------------------------
-- Common utilities                                                          --
-------------------------------------------------------------------------------

-- | Wrapper that is used by 'typeDependency'' and 'exprDependencies'' to
--   remember whether a name is a variable or constructor name such that
--   'typeVars', 'typeCons', 'vars' and 'cons' can filter them appropriatly.
data DependencyName = VarName HS.Name | ConName HS.Name
  deriving (Eq, Ord, Show)

-- | Smart constructor for a set that contains the name of a single (type)
--   variable dependency.
varName :: HS.Name -> Set DependencyName
varName = Set.singleton . VarName

-- | Smart constructor for a set that contains the name of a single (type)
--   constructor dependency.
conName :: HS.Name -> Set DependencyName
conName = Set.singleton . ConName

-- | Gets the 'HS.Name' wrapped by the given dependency name.
unwrap :: DependencyName -> HS.Name
unwrap (VarName name) = name
unwrap (ConName name) = name

-- | Gets a list of all 'HS.Names' wrapped by dependency names in the
--   given set.
unwrapSet :: Set DependencyName -> [HS.Name]
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

-- | Extracts the names of all type variables and type constructors used in
--   the given type expression.
--
--   This also includes the names of predefied constructors.
typeDependencies :: HS.Type -> [HS.Name]
typeDependencies = unwrapSet . typeDependencies'

-- | Extracts the names of all type variables used in the given type
--   expression.
typeVars :: HS.Type -> [HS.Name]
typeVars = unwrapSet . Set.filter isVarName . typeDependencies'

-- | Extracts the names of all type constructors used in the given type
--   expression.
--
--   This also includes the names of predefined constructors.
typeCons :: HS.Type -> [HS.Name]
typeCons = unwrapSet . Set.filter isConName . typeDependencies'

-- | Extracts the names of all type variables and type constructors used in
--   the given type expression and remembers for every name whether it is
--   the name of a type variable or type constructor.
typeDependencies' :: HS.Type -> Set DependencyName
typeDependencies' (HS.TypeVar _ ident) = varName (HS.Ident ident)
typeDependencies' (HS.TypeCon _ name ) = conName name
typeDependencies' (HS.TypeApp _ t1 t2) =
  typeDependencies' t1 `Set.union` typeDependencies' t2
typeDependencies' (HS.TypeFunc _ t1 t2) =
  typeDependencies' t1 `Set.union` typeDependencies' t2

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Extracts the names of all variables, functions and constructors used in
--   the given expression.
--
--   This also includes the names of predefined functions, error terms like
--   @undefined@ and @error@ as well as constructors.
exprDependencies :: HS.Expr -> [HS.Name]
exprDependencies = unwrapSet . exprDependencies'

-- | Extracts the names of all variables used in the given expression.
--
--   This also includes the names of functions, predefined functions and the
--   error terms @undefined@ and @error@.
vars :: HS.Expr -> [HS.Name]
vars = unwrapSet . Set.filter isVarName . exprDependencies'

-- | Extracts the names of all constructors used in the given expression.
--
--   This also includes predefined constructors.
cons :: HS.Expr -> [HS.Name]
cons = unwrapSet . Set.filter isConName . exprDependencies'

-- | Extracts the names of all variables, functions and constructors used in
--   the given expression and remembers for every name whether it is the name
--   of a variable (or function) or constructor.
exprDependencies' :: HS.Expr -> Set DependencyName
exprDependencies' (HS.Var _ name) = varName name
exprDependencies' (HS.Con _ name) = conName name
exprDependencies' (HS.App _ e1 e2) =
  exprDependencies' e1 `Set.union` exprDependencies' e2
exprDependencies' (HS.InfixApp _ e1 op e2) =
  Set.unions (opDependencies op : map exprDependencies' [e1, e2])
exprDependencies' (HS.LeftSection _ e1 op) =
  opDependencies op `Set.union` exprDependencies' e1
exprDependencies' (HS.RightSection _ op e2) =
  opDependencies op `Set.union` exprDependencies' e2
exprDependencies' (HS.NegApp _ expr) = exprDependencies' expr
exprDependencies' (HS.If _ e1 e2 e3) =
  Set.unions (map exprDependencies' [e1, e2, e3])
exprDependencies' (HS.Case _ expr alts) =
  Set.unions (exprDependencies' expr : map altDependencies alts)
exprDependencies' (HS.Undefined _   ) = varName (HS.Ident "undefined")
exprDependencies' (HS.ErrorExpr  _ _) = conName (HS.Ident "error")
exprDependencies' (HS.IntLiteral _ _) = Set.empty
exprDependencies' (HS.Lambda _ args expr) =
  withoutArgs args (exprDependencies' expr)

-- | Extracts the names of all variables, functions and constructors used in
--   the given alternative of a @case@-expression.
altDependencies :: HS.Alt -> Set DependencyName
altDependencies (HS.Alt _ (HS.ConPat _ name) args expr) =
  Set.insert (ConName name) (withoutArgs args (exprDependencies' expr))

-- | Gets the name for a function or constructor used in infix notation.
opDependencies :: HS.Op -> Set DependencyName
opDependencies (HS.VarOp _ name) = varName name
opDependencies (HS.ConOp _ name) = conName name

-------------------------------------------------------------------------------
-- Type declarations                                   --
-------------------------------------------------------------------------------

-- | Extracts the dependencies of the given data type or type synonym
--   declaration on type constructors (if a constructor contains undeclared
--   type variables, the returned set contains the names of those type
--   variables as well).
--
--   Returns an empty set if the given declaration is not a type declaration.
typeDeclDependencies :: HS.Decl -> [HS.Name]
typeDeclDependencies = unwrapSet . typeDeclDependencies'

-- | Extracts the dependencies of the given data type or type synonym
--   declaration on type constructors (and undeclared type variables) and
--   remebers for every name whether it is the name of a type variable or
--   of a type constructor.
--
--   Returns an empty set if the given declaration is not a type declaration.
typeDeclDependencies' :: HS.Decl -> Set DependencyName
typeDeclDependencies' (HS.TypeDecl _ _ typeArgs typeExpr) =
  withoutTypeArgs typeArgs (typeDependencies' typeExpr)
typeDeclDependencies' (HS.DataDecl _ _ typeArgs conDecls) =
  withoutTypeArgs typeArgs (Set.unions (map conDeclDependencies conDecls))
typeDeclDependencies' _ = Set.empty

-- | Extracts the dependencies of the field types of the given constructor
--   declaration.
conDeclDependencies :: HS.ConDecl -> Set DependencyName
conDeclDependencies (HS.ConDecl _ _ types) =
  Set.unions (map typeDependencies' types)

-- | Removes the names of the given type variable declarations from a set
--   of dependency names.
withoutTypeArgs :: [HS.TypeVarDecl] -> Set DependencyName -> Set DependencyName
withoutTypeArgs args set = set \\ Set.fromList (map varPatToName args)
 where
  varPatToName :: HS.TypeVarDecl -> DependencyName
  varPatToName (HS.DeclIdent _ ident) = VarName (HS.Ident ident)

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

-- | Extracts the dependencies of the given function declaration on
--   constructors and other functions.
--
--   Returns an empty set if the given declaration is not a function
--   declaration.
funcDeclDependencies :: HS.Decl -> [HS.Name]
funcDeclDependencies = unwrapSet . funcDeclDependencies'

-- | Extracts the dependencies of the given function declaration on
--   constructors and other functions and remembers for every name whether it
--   is the name of a function or constructor.
--
--   Returns an empty set if the given declaration is not a function
--   declaration.
funcDeclDependencies' :: HS.Decl -> Set DependencyName
funcDeclDependencies' (HS.FuncDecl _ _ args expr) =
  withoutArgs args (exprDependencies' expr)
funcDeclEntries _ = Set.empty

-- | Removes the names for the given variable patterns from a set of
--   dependencies.
withoutArgs :: [HS.VarPat] -> Set DependencyName -> Set DependencyName
withoutArgs args set = set \\ Set.fromList (map varPatToName args)
 where
  varPatToName :: HS.VarPat -> DependencyName
  varPatToName (HS.VarPat _ ident) = VarName (HS.Ident ident)
