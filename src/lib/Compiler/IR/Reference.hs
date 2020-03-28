-- | This module contains functions to extract the names of (type) constructors
--   and variables that are referenced by AST nodes such as expressions and
--   type expressions.
--
--   These functions are used to construct the dependency graph and to find
--   free (type) variables in (type) expressions.

module Compiler.IR.Reference
  ( -- * References
    Ref(..)
  , refScope
  , refName
  , isVarRef
  , isConRef
  , isTypeRef
  , isValueRef
    -- * Finding references
  , HasRefs
  , refs
  , typeRefs
  , valueRefs
    -- * Free type variables
  , freeTypeVars
  , freeTypeVarSet
    -- * Free variables
  , freeVars
  , freeVarSet
  )
where

import           Data.Composition               ( (.:) )
import qualified Data.Foldable                 as OSet
                                                ( toList )
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set
import           Data.Set.Ordered               ( OSet
                                                , (\\)
                                                )
import qualified Data.Set.Ordered              as OSet

import           Compiler.Environment.Scope
import qualified Compiler.IR.Syntax            as HS
import           Compiler.Util.Predicate        ( (.&&.) )

-------------------------------------------------------------------------------
-- References                                                                --
-------------------------------------------------------------------------------

-- | Wrapper that is used to remember whether a name refers to a variable or
--   constructor.
--
--   The wrapped names are 'ScopedName's such that we can use the same function
--   to collect the type- and value-level references.
data Ref = VarRef { unwrapRef :: ScopedName }
         | ConRef { unwrapRef :: ScopedName }
 deriving (Eq, Ord, Show)

-- | Smart constructor for a reference to a variable or type variable
--   with the given name.
varRef :: Scope -> HS.QName -> Ref
varRef = VarRef .: (,)

-- | Smart constructor for a reference to a constructor or type constructor
--   with the given name.
conRef :: Scope -> HS.QName -> Ref
conRef = ConRef .: (,)

-- | Tests whether the given reference refers to a variable or type variable.
isVarRef :: Ref -> Bool
isVarRef (VarRef _) = True
isVarRef (ConRef _) = False

-- | Tests whether the given reference refers to a constructor or
--   type constructor.
isConRef :: Ref -> Bool
isConRef (VarRef _) = False
isConRef (ConRef _) = True

-- | Tests whether the given reference refers to a type-level entry.
isTypeRef :: Ref -> Bool
isTypeRef = (== TypeScope) . refScope

-- | Tests whether the given reference refers to a value-level entry.
isValueRef :: Ref -> Bool
isValueRef = (== ValueScope) . refScope

-- | Unwraps the given reference and discards the name.
refScope :: Ref -> Scope
refScope = fst . unwrapRef

-- | Unwraps the given reference and discards the scope information.
refName :: Ref -> HS.QName
refName = snd . unwrapRef

-------------------------------------------------------------------------------
-- Reference sets                                                            --
-------------------------------------------------------------------------------

-- | A set of references.
--
--   Reference sets are ordered sets such that the order of extracted
--   references does not depend on how the names are ordered but on the
--   order they appear in the expression or type expression.
type RefSet = OSet Ref

-- | A set that contains no references.
empty :: RefSet
empty = OSet.empty

-- | Smart constructor for a set that contains a single reference to a
--   variable or type variable.
varRefSet :: Scope -> HS.QName -> RefSet
varRefSet = OSet.singleton . VarRef .: (,)

-- | Smart constructor for a set that contains a single reference to a
--   constructor or type constructor.
conRefSet :: Scope -> HS.QName -> RefSet
conRefSet = OSet.singleton . ConRef .: (,)

-- | Inserts a reference before all elements in the given set.
insertBefore :: Ref -> RefSet -> RefSet
insertBefore = (OSet.|<)

-- | When a reference is an element of two reference sets, the indices of the
--   first set take precedence in the union of both sets.
--
--   If both the left and right subtree of an expression contain the same
--   reference, we sort the reference from the left subtree before the
--   references from the right subtree such that references are extracted in
--   left to right order.
union :: RefSet -> RefSet -> RefSet
union = (OSet.|<>)

-- | Calculates the union of the given sets using 'union'.
unions :: [RefSet] -> RefSet
unions = foldr union OSet.empty

-------------------------------------------------------------------------------
-- Type class                                                                --
-------------------------------------------------------------------------------

-- | Type class for AST nodes that contain references to (type) variables and
--   constructors.
class HasRefs a where
  -- | Recursively gets all references in the given node.
  refSet :: a -> RefSet

-- | Utility instance to get the references of an optional value.
--
--   Returns references of the wrapped value or an empty set for @Nothing@.
instance HasRefs a => HasRefs (Maybe a) where
  refSet = maybe empty refSet

-- | Utility instance to get the references of all elements in a list.
instance HasRefs a => HasRefs [a] where
  refSet = unions . map refSet

-- | Gets all references to variables, constructors, type variables and type
--   constructors in the given node as they occur from left to right.
refs :: HasRefs a => a -> [Ref]
refs = OSet.toList . refSet

-- | Gets the names of all type variables and type constructors the given
--   node refers to.
typeRefs :: HasRefs a => a -> [HS.QName]
typeRefs = map refName . filter isTypeRef . refs

-- | gets the names of all variable and constructors the given node refers to.
valueRefs :: HasRefs a => a -> [HS.QName]
valueRefs = map refName . filter isValueRef . refs

-------------------------------------------------------------------------------
-- Types and type schemas                                                    --
-------------------------------------------------------------------------------

-- | Type expressions refer to the used type variables and type constructors.
instance HasRefs HS.Type where
  refSet (HS.TypeVar _ ident) =
    varRefSet TypeScope (HS.UnQual (HS.Ident ident))
  refSet (HS.TypeCon _ conName) = conRefSet TypeScope conName
  refSet (HS.TypeApp  _ t1 t2 ) = refSet t1 `union` refSet t2
  refSet (HS.FuncType _ t1 t2 ) = refSet t1 `union` refSet t2

-- | Type schemas refer to the types it's type expression refers to but
--   not to the type variables that are bound by the type schema.
instance HasRefs HS.TypeSchema where
  refSet (HS.TypeSchema _ typeArgs typeExpr) =
    withoutTypeArgs typeArgs (refSet typeExpr)

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Expression refer to the used variables and constructors as wells as the
--   types used in type signatures and visible type applications.
--
--   The error terms @undefined@ and @error "<msg>"@ refer to the functions
--   'HS.undefinedFuncName' and 'HS.errorFuncName' respectively.
instance HasRefs HS.Expr where
  refSet (HS.Var _ varName exprType) =
    varRef ValueScope varName `insertBefore` refSet exprType
  refSet (HS.Con _ conName exprType) =
    conRef ValueScope conName `insertBefore` refSet exprType
  refSet (HS.App _ e1 e2 exprType) = refSet [e1, e2] `union` refSet exprType
  refSet (HS.TypeAppExpr _ expr typeExpr exprType) =
    unions [refSet expr, refSet typeExpr, refSet exprType]
  refSet (HS.If _ e1 e2 e3 exprType) =
    refSet [e1, e2, e3] `union` refSet exprType
  refSet (HS.Case _ scrutinee alts exprType) =
    unions [refSet scrutinee, refSet alts, refSet exprType]
  refSet (HS.Undefined _ exprType) =
    varRef ValueScope HS.undefinedFuncName `insertBefore` refSet exprType
  refSet (HS.ErrorExpr _ _ exprType) =
    varRef ValueScope HS.errorFuncName `insertBefore` refSet exprType
  refSet (HS.IntLiteral _ _ exprType) = refSet exprType
  refSet (HS.Lambda _ args expr exprType) =
    unions [refSet args, withoutArgs args (refSet expr), refSet exprType]

-- | @case@ expression alternatives refer to the matched constructor, the types
--   the type annotations of the variable patterns refer to and the references
--   of the right-hand side that are not bound by the variable patterns.
instance HasRefs HS.Alt where
  refSet (HS.Alt _ conPat varPats rhs) =
    unions [refSet conPat, refSet varPats, withoutArgs varPats (refSet rhs)]

-- | Constructor patterns refer to the matched constructor.
instance HasRefs HS.ConPat where
  refSet = conRefSet ValueScope . HS.conPatName

-- | Variable patterns refer to the types used in their type annotation.
instance HasRefs HS.VarPat where
  refSet = refSet . HS.varPatType

-------------------------------------------------------------------------------
-- Type declarations                                                         --
-------------------------------------------------------------------------------

-- | Data type declarations refer to the types their constructors refer to and
--   type synonym declarations refer to the types it's right hand side refers
--   to. Both don't refer to type variables that are bound by their type
--   arguments.
instance HasRefs HS.TypeDecl where
  refSet (HS.DataDecl _ _ typeArgs cons) =
    withoutTypeArgs typeArgs (refSet cons)
  refSet (HS.TypeSynDecl _ _ typeArgs typeSyn) =
    withoutTypeArgs typeArgs (refSet typeSyn)

-- | Constructor declarations refer to the types their field types refer to.
instance HasRefs HS.ConDecl where
  refSet = refSet . HS.conDeclFields

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

-- | Function declarations refer to the types their argument and return type
--   annotations refer to as well as the references of their right-hand side
--   except for the (type) variables bound by the function's (type) arguments.
instance HasRefs HS.FuncDecl where
  refSet (HS.FuncDecl _ _ typeArgs args rhs retType) =
    withoutTypeArgs typeArgs
      $       refSet args
      `union` withoutArgs args (refSet rhs)
      `union` refSet retType

-------------------------------------------------------------------------------
-- Removing bound (type) variables                                           --
-------------------------------------------------------------------------------

-- | Removes the references to type variables that are bound by the given
--   type variable declarations from the given set.
withoutTypeArgs :: [HS.TypeVarDecl] -> RefSet -> RefSet
withoutTypeArgs typeArgs set =
  set \\ OSet.fromList (map (varRef TypeScope . HS.typeVarDeclQName) typeArgs)

-- | Removes the references to variables that are bound by the given variable
--   patterns from the given set.
withoutArgs :: [HS.VarPat] -> RefSet -> RefSet
withoutArgs args set =
  set \\ OSet.fromList (map (varRef ValueScope . HS.varPatQName) args)

-------------------------------------------------------------------------------
-- Free type variables                                                       --
-------------------------------------------------------------------------------

-- | The type variables that occur freely in the given node from left to right.
freeTypeVars :: HasRefs a => a -> [HS.QName]
freeTypeVars = map refName . filter (isVarRef .&&. isTypeRef) . refs

-- | The type variables that occur freely in the given node.
freeTypeVarSet :: HasRefs a => a -> Set HS.QName
freeTypeVarSet =
  Set.map refName . Set.filter (isVarRef .&&. isTypeRef) . OSet.toSet . refSet

-------------------------------------------------------------------------------
-- Free variables                                                            --
-------------------------------------------------------------------------------

-- | The variables that occur freely in the given node from left to right.
freeVars :: HasRefs a => a -> [HS.QName]
freeVars = map refName . filter (isVarRef .&&. isValueRef) . refs

-- | The variables that occur freely in the given node.
freeVarSet :: HasRefs a => a -> Set HS.QName
freeVarSet =
  Set.map refName . Set.filter (isVarRef .&&. isValueRef) . OSet.toSet . refSet
