-- | This module contains functions to extract the names of (type) constructors
--   and variables that are referenced by AST nodes such as expressions and
--   type expressions.
--
--   These functions are used to construct the dependency graph and to find
--   free (type) variables in (type) expressions.

module FreeC.IR.Reference
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
import           Data.Maybe                     ( fromJust )
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set
import           Data.Set.Ordered               ( OSet
                                                , (\\)
                                                )
import qualified Data.Set.Ordered              as OSet

import qualified FreeC.IR.Base.Prelude         as IR.Prelude
import qualified FreeC.IR.Syntax               as IR
import           FreeC.Util.Predicate           ( (.&&.) )

-------------------------------------------------------------------------------
-- References                                                                --
-------------------------------------------------------------------------------

-- | Wrapper that is used to remember whether a name refers to a variable or
--   constructor.
--
--   The wrapped names are 'IR.ScopedName's such that we can use the same
--   function to collect the type- and value-level references.
data Ref
  = VarRef { unwrapRef :: IR.ScopedName }
  | ConRef { unwrapRef :: IR.ScopedName }
 deriving (Eq, Ord, Show)

-- | Smart constructor for a reference to a variable or type variable
--   with the given name.
varRef :: IR.Scope -> IR.QName -> Ref
varRef = VarRef .: (,)

-- | Smart constructor for a reference to a constructor or type constructor
--   with the given name.
conRef :: IR.Scope -> IR.QName -> Ref
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
isTypeRef = (== IR.TypeScope) . refScope

-- | Tests whether the given reference refers to a value-level entry.
isValueRef :: Ref -> Bool
isValueRef = (== IR.ValueScope) . refScope

-- | Unwraps the given reference and discards the name.
refScope :: Ref -> IR.Scope
refScope = fst . unwrapRef

-- | Unwraps the given reference and discards the scope information.
refName :: Ref -> IR.QName
refName = snd . unwrapRef

-- | Like 'refName' but unwraps the identifier of the name.
--
--   Fails if the given reference is a symbol.
refIdent :: Ref -> String
refIdent = fromJust . IR.identFromQName . refName

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
varRefSet :: IR.Scope -> IR.QName -> RefSet
varRefSet = OSet.singleton . VarRef .: (,)

-- | Smart constructor for a set that contains a single reference to a
--   constructor or type constructor.
conRefSet :: IR.Scope -> IR.QName -> RefSet
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
typeRefs :: HasRefs a => a -> [IR.QName]
typeRefs = map refName . filter isTypeRef . refs

-- | gets the names of all variable and constructors the given node refers to.
valueRefs :: HasRefs a => a -> [IR.QName]
valueRefs = map refName . filter isValueRef . refs

-------------------------------------------------------------------------------
-- Types and type schemas                                                    --
-------------------------------------------------------------------------------

-- | Type expressions refer to the used type variables and type constructors.
instance HasRefs IR.Type where
  refSet (IR.TypeVar _ ident) =
    varRefSet IR.TypeScope (IR.UnQual (IR.Ident ident))
  refSet (IR.TypeCon _ conName) = conRefSet IR.TypeScope conName
  refSet (IR.TypeApp  _ t1 t2 ) = refSet t1 `union` refSet t2
  refSet (IR.FuncType _ t1 t2 ) = refSet t1 `union` refSet t2

-- | Type schemas refer to the types it's type expression refers to but
--   not to the type variables that are bound by the type schema.
instance HasRefs IR.TypeSchema where
  refSet (IR.TypeSchema _ typeArgs typeExpr) =
    withoutTypeArgs typeArgs (refSet typeExpr)

-------------------------------------------------------------------------------
-- Expressions                                                               --
-------------------------------------------------------------------------------

-- | Expression refer to the used variables and constructors as wells as the
--   types used in type signatures and visible type applications.
--
--   The error terms @undefined@ and @error "<msg>"@ refer to the functions
--   'IR.Prelude.undefinedFuncName' and 'IR.Prelude.errorFuncName' respectively.
instance HasRefs IR.Expr where
  refSet (IR.Var _ varName exprType) =
    varRef IR.ValueScope varName `insertBefore` refSet exprType
  refSet (IR.Con _ conName exprType) =
    conRef IR.ValueScope conName `insertBefore` refSet exprType
  refSet (IR.App _ e1 e2 exprType) = refSet [e1, e2] `union` refSet exprType
  refSet (IR.TypeAppExpr _ expr typeExpr exprType) =
    unions [refSet expr, refSet typeExpr, refSet exprType]
  refSet (IR.If _ e1 e2 e3 exprType) =
    refSet [e1, e2, e3] `union` refSet exprType
  refSet (IR.Case _ scrutinee alts exprType) =
    unions [refSet scrutinee, refSet alts, refSet exprType]
  refSet (IR.Undefined _ exprType) =
    varRef IR.ValueScope IR.Prelude.undefinedFuncName
      `insertBefore` refSet exprType
  refSet (IR.ErrorExpr _ _ exprType) =
    varRef IR.ValueScope IR.Prelude.errorFuncName `insertBefore` refSet exprType
  refSet (IR.IntLiteral _ _ exprType) = refSet exprType
  refSet (IR.Lambda _ args expr exprType) =
    unions [refSet args, withoutArgs args (refSet expr), refSet exprType]
  refSet (IR.Let _  binds expr  exprType) =
    unions [refSet expr, refSet binds, refSet exprType]

-- | @case@ expression alternatives refer to the matched constructor, the types
--   the type annotations of the variable patterns refer to and the references
--   of the right-hand side that are not bound by the variable patterns.
instance HasRefs IR.Alt where
  refSet (IR.Alt _ conPat varPats rhs) =
    unions [refSet conPat, refSet varPats, withoutArgs varPats (refSet rhs)]

-- | Constructor patterns refer to the matched constructor.
instance HasRefs IR.ConPat where
  refSet = conRefSet IR.ValueScope . IR.conPatName

-- | Variable patterns refer to the types used in their type annotation.
instance HasRefs IR.VarPat where
  refSet = refSet . IR.varPatType

-- | Bindings refer to the used variable pattern and the types used in type
-- signatures.
instance HasRefs IR.Bind where
  refSet b = refSet (IR.bindVarPat b) `union` refSet (IR.bindExpr b)

-------------------------------------------------------------------------------
-- Type declarations                                                         --
-------------------------------------------------------------------------------

-- | Data type declarations refer to the types their constructors refer to and
--   type synonym declarations refer to the types it's right-hand side refers
--   to. Both don't refer to type variables that are bound by their type
--   arguments.
instance HasRefs IR.TypeDecl where
  refSet (IR.DataDecl _ _ typeArgs cons) =
    withoutTypeArgs typeArgs (refSet cons)
  refSet (IR.TypeSynDecl _ _ typeArgs typeSyn) =
    withoutTypeArgs typeArgs (refSet typeSyn)

-- | Constructor declarations refer to the types their field types refer to.
instance HasRefs IR.ConDecl where
  refSet = refSet . IR.conDeclFields

-------------------------------------------------------------------------------
-- Function declarations                                                     --
-------------------------------------------------------------------------------

-- | Function declarations refer to the types their argument and return type
--   annotations refer to as well as the references of their right-hand side
--   except for the (type) variables bound by the function's (type) arguments.
instance HasRefs IR.FuncDecl where
  refSet (IR.FuncDecl _ _ typeArgs args retType rhs) =
    withoutTypeArgs typeArgs
      $       refSet args
      `union` refSet retType
      `union` withoutArgs args (refSet rhs)

-------------------------------------------------------------------------------
-- Removing bound (type) variables                                           --
-------------------------------------------------------------------------------

-- | Removes the references to type variables that are bound by the given
--   type variable declarations from the given set.
withoutTypeArgs :: [IR.TypeVarDecl] -> RefSet -> RefSet
withoutTypeArgs typeArgs set = set
  \\ OSet.fromList (map (varRef IR.TypeScope . IR.typeVarDeclQName) typeArgs)

-- | Removes the references to variables that are bound by the given variable
--   patterns from the given set.
withoutArgs :: [IR.VarPat] -> RefSet -> RefSet
withoutArgs args set =
  set \\ OSet.fromList (map (varRef IR.ValueScope . IR.varPatQName) args)

-------------------------------------------------------------------------------
-- Free type variables                                                       --
-------------------------------------------------------------------------------

-- | The type variables that occur freely in the given node from left to right.
freeTypeVars :: HasRefs a => a -> [IR.TypeVarIdent]
freeTypeVars = map refIdent . filter (isVarRef .&&. isTypeRef) . refs

-- | The type variables that occur freely in the given node.
freeTypeVarSet :: HasRefs a => a -> Set IR.TypeVarIdent
freeTypeVarSet =
  Set.map refIdent . Set.filter (isVarRef .&&. isTypeRef) . OSet.toSet . refSet

-------------------------------------------------------------------------------
-- Free variables                                                            --
-------------------------------------------------------------------------------

-- | The variables that occur freely in the given node from left to right.
freeVars :: HasRefs a => a -> [IR.QName]
freeVars = map refName . filter (isVarRef .&&. isValueRef) . refs

-- | The variables that occur freely in the given node.
freeVarSet :: HasRefs a => a -> Set IR.QName
freeVarSet =
  Set.map refName . Set.filter (isVarRef .&&. isValueRef) . OSet.toSet . refSet
