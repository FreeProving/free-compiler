-- | This module contains a definition for a custom equality of IR AST nodes.
--   Two AST nodes are called 'similar' if they are equal modulo renaming
--   of bound variables. The source location information is also ignored.
--
--   == Definition Renaming
--
--   A 'Renaming' is a mapping @{ x₁ ↦ y₁, …, xₙ ↦ yₙ }@ from variables
--   @x₁, …, xₙ@ in one AST to variables @y₁, …, yₙ@ in another AST.
--   Note that variables and type variables are considered distict even
--   if they have the same name.
--
--   == Definition: Free Variables in Renaming
--
--   A variable @x@ is 'leftFree' in a 'Renaming' @Γ@ if there is no
--   variable @y@ such that @x ↦ y ∈ Γ@. Analogously a variable @y@ is
--   'rightFree' in a 'Renaming' @Γ@ if there is no variable @x@ such
--   that @x ↦ y ∈ Γ@. We write @z ∈ free(Γ)@ if @z@ is both 'leftFree'
--   and 'rightFree'.
--
--   == Notation
--
--   If two nodes @n@ and @m@ are similar under a 'Renaming' @Γ@ we write
--   @Γ ⊢ n ≈ m@. Whether two nodes are equal or not can be determined
--   from the inference system described in the comments for the 'Similar'
--   instances below.
module FreeC.IR.Similar
  ( Similar
  , similar
  , notSimilar
  )
where

import           Control.Monad.Extra            ( andM )
import           Data.Composition               ( (.:) )
import           Data.Map.Strict                ( Map )
import qualified Data.Map.Strict               as Map
import           Data.Set                       ( Set )
import qualified Data.Set                      as Set

import qualified FreeC.IR.Syntax               as IR
import           FreeC.Util.Predicate           ( (.&&.) )

-------------------------------------------------------------------------------
-- Renaming                                                                  --
-------------------------------------------------------------------------------

-- | A mapping from names of bound variable names in one AST to the
--   corresponding names in the second AST.
--
--   Since expressions and types can be mixed, we have to keep track of the
--   scopes the variables have been bound in (i.e., use 'IR.IR.ScopedName's).
--
--   Since we have to perform lookups both in the domain and the image of
--   the mapping, we explicitly keep track of the variables bound in the
--   in the right AST. The variables bound in the left AST can already
--   be looked up in the 'renameMap'.
data Renaming = Renaming
  { renameMap     :: Map IR.ScopedName IR.QName
    -- ^ Maps variables bound in the left AST to variables
    --   bound in the right AST.
  , rightBoundSet :: Set IR.ScopedName
    -- ^ The variables bound in the right AST.
  }

-- | An empty mapping of variable names.
emptyRenaming :: Renaming
emptyRenaming = Renaming { renameMap = Map.empty, rightBoundSet = Set.empty }

-- | The variables bound by the left AST.
leftBoundSet :: Renaming -> Set IR.ScopedName
leftBoundSet = Map.keysSet . renameMap

-- | Tests whether the given variable is free in the left AST.
leftFree :: IR.ScopedName -> Renaming -> Bool
leftFree name renaming = name `Set.notMember` leftBoundSet renaming

-- | Tests whether the given variable is free in the right AST.
rightFree :: IR.ScopedName -> Renaming -> Bool
rightFree name renaming = name `Set.notMember` rightBoundSet renaming

-- | Tests whether two variables in the given scope are similar, i.e.,
--   they are either free in their ASTs and equal or they are mapped
--   to each other (and therefore both not free).
similarVars :: IR.Scope -> IR.QName -> IR.QName -> Renaming -> Bool
similarVars scope x y renaming
  | leftFree x' renaming && rightFree y' renaming = x == y
  | otherwise = Map.lookup x' (renameMap renaming) == Just y
 where
  x', y' :: IR.ScopedName
  x' = (scope, x)
  y' = (scope, y)

-- | Extends a renaming by the corresponding pairs of variable names from the
--   two given lists.
extendRenaming :: IR.Scope -> [IR.QName] -> [IR.QName] -> Renaming -> Renaming
extendRenaming scope xs ys renaming = Renaming
  { renameMap     = Map.fromList (zip xs' ys) `Map.union` renameMap renaming
  , rightBoundSet = Set.fromList ys' `Set.union` rightBoundSet renaming
  }
 where
  xs', ys' :: [IR.ScopedName]
  xs' = map ((,) scope) xs
  ys' = map ((,) scope) ys

-------------------------------------------------------------------------------
-- Similarity test                                                           --
-------------------------------------------------------------------------------

-- | A type class for AST nodes that can be tested for similarity.
class Similar node where
  -- | Like 'similar' but the first argument is the 'Renaming' of bound
  --   variables.
  similar' :: node -> node -> Renaming -> Bool

-- | Tests whether two AST nodes are similar, i.e., if they are equal
--   except for renaming of bound variables.
similar :: Similar node => node -> node -> Bool
similar n m = similar' n m emptyRenaming

-- | The negation of 'similar'.
notSimilar :: Similar node => node -> node -> Bool
notSimilar = not .: similar

-------------------------------------------------------------------------------
-- Utility instances                                                         --
-------------------------------------------------------------------------------

-- | Two optional nodes are similar when they are either both not present
--   or both are present and similar.
--
--   >                                Γ ⊢ x ≈ y
--   > ———————————————————————  —————————————————————
--   >  Γ ⊢ Nothing ≈ Nothing    Γ ⊢ Just x ≈ Just y
instance Similar node => Similar (Maybe node) where
  similar' Nothing  Nothing  = const True
  similar' (Just n) (Just m) = similar' n m
  similar' _        _        = const False

-- | Two lists of nodes are similar if the corresponding elements are similar
--   and each element has a corresponding element (i.e., the lists are of the
--   same length).
--
--   >   Γ ⊢ x₁ ≈ y₁, …, Γ ⊢ xₙ ≈ yₙ
--   > ———————————————————————————————
--   >  Γ ⊢ [x₁, …, xₙ] ≈ [y₁, …, yₙ]
instance Similar node => Similar [node] where
  similar' ms ns | length ms == length ns = andM (zipWith similar' ms ns)
                 | otherwise              = const False

-------------------------------------------------------------------------------
-- Similarity test for types                                                 --
-------------------------------------------------------------------------------

-- | The similarity relation of type expressions is governed by the
--   the following inference rules.
--
--   * Type constructors are only similar to themselves.
--
--       > ———————————
--       >  Γ ⊢ T ≈ T
--
--   * A free type variable @α@ is similar to itself.
--
--        >  α ∈ free(Γ)
--        > —————————————
--        >  Γ ⊢ α ≈ α
--
--   * Two type variables @α@ and @β@ are similar under a renaming @Γ@ if they
--     are mapped to each other by @Γ@.
--
--        >  α ↦ β ∈ Γ
--        > ———————————
--        >  Γ ⊢ α ≈ β
--
--   * Two type applications are similar if the type constructor and type
--     argument are similar.
--
--        >  Γ ⊢ τ₁ ≈ τ'₁ , Γ ⊢ τ₂ ≈ τ'₂
--        > —————————————————————————————
--        >      Γ ⊢ τ₁ τ₂ ≈ τ'₁ τ'₂
--
--   * Two function types are similar if their argument and return types
--     are similar.
--
--        >  Γ ⊢ τ₁ ≈ τ'₁ , Γ ⊢ τ₂ ≈ τ'₂
--        > —————————————————————————————
--        >   Γ ⊢ τ₁ -> τ₂ ≈ τ'₁ -> τ'₂
instance Similar IR.Type where
  similar' (IR.TypeCon _ c1) (IR.TypeCon _ c2) = const (c1 == c2)
  similar' (IR.TypeVar _ v1) (IR.TypeVar _ v2) =
    similarVars IR.TypeScope (IR.UnQual (IR.Ident v1)) (IR.UnQual (IR.Ident v2))
  similar' (IR.TypeApp _ s1 s2) (IR.TypeApp _ t1 t2) =
    similar' s1 t1 .&&. similar' s2 t2
  similar' (IR.FuncType _ s1 s2) (IR.FuncType _ t1 t2) =
    similar' s1 t1 .&&. similar' s2 t2

  -- Combinations of different constructors are not similar.
  similar' (IR.TypeCon _ _   ) _ = const False
  similar' (IR.TypeVar _ _   ) _ = const False
  similar' (IR.TypeApp  _ _ _) _ = const False
  similar' (IR.FuncType _ _ _) _ = const False

-- | Two type schemas are similar if their abstracted types are similar
--   under an extend 'Renaming' that maps the corresponding type arguments
--   to each other.
--
--   >     Γ ∪ { α₁ ↦ β₁, …, αₙ ↦ βₙ } ⊢ τ ≈ τ'
--   > ————————————————————————————————————————————
--   >  Γ ⊢ forall α₁ … αₙ. τ ≈ forall β₁ … βₙ. τ'
instance Similar IR.TypeSchema where
  similar' (IR.TypeSchema _ as t1) (IR.TypeSchema _ bs t2) =
    let ns = map IR.typeVarDeclQName as
        ms = map IR.typeVarDeclQName bs
    in  similar' t1 t2 . extendRenaming IR.TypeScope ns ms

-------------------------------------------------------------------------------
-- Similarity test for expressions                                           --
-------------------------------------------------------------------------------

-- | The similarity relation of expressions is governed by the the following
--   inference rules
--
--    * Expressions with type annotations are similar if the annotated
--      expressions are similar and their annotations are similar.
--
--        >  Γ ⊢ τ ≈ τ', Γ ⊢ e ≈ f
--        > ———————————————————————
--        >  Γ ⊢ e :: τ ≈ f :: τ'
--
--    * For all variables @x@ and @y@, @x@ and @y@ are similar under a
--      renaming @Γ@ if they are mapped to each other by @Γ@.
--
--        >  x ↦ y ∈ Γ
--        > ———————————
--        >  Γ ⊢ x ≈ y
--
--    * A free variable @x@ is similar to itself.
--
--        >  x ∈ free(Γ)
--        > —————————————
--        >  Γ ⊢ x ≈ x
--
--    * Two lambda abstractions are similar if their right-hand sides are
--      similar under an extended 'Renaming' that maps the variable patterns
--      from the first lambda abstraction to the arguments of the second one.
--      Furthermore, the types the lambda abstraction's arguments have been
--      annotated with must be similar (if there are any).
--
--        >  Γ ∪ { x₁ ↦ y₁, …, xₙ ↦ yₙ } ⊢ e ≈ f, Γ ⊢ p₁ ≈ q₁, …, Γ ⊢ pₙ ≈ qₙ
--        > ——————————————————————————————————————————————————————————————————
--        >                 Γ ⊢ \p₁ … pₙ -> e ≈ \q₁ … qₙ -> f
--
--        where @xᵢ@ and @yᵢ@ denote the names of the variables bound by the
--        patterns @pᵢ@ and @qᵢ@ respectively.
--
--    * Two application expressions are similar if the callees and the
--      arguments are similar.
--
--        >  Γ ⊢ e₁ ≈ f₁, Γ ⊢ e₂ ≈ f₂
--        > ——————————————————————————
--        >     Γ ⊢ e₁ e₂ ≈ f₁ f₂
--
--    * Two visible type application expressions are similar if the visibly
--      applied expressions and the type arguments are similar.
--
--        >  Γ ⊢ e ≈ f, Γ ⊢ τ ≈ τ'
--        > ———————————————————————
--        >     Γ ⊢ e @τ ≈ f @τ'
--
--    * Two @case@ expressions are similar if the expressions they match are
--      similar and their alternatives are pairwise similar. Note that the
--      order of the alternatives is important.
--
--        >  Γ ⊢ e ≈ f,      Γ ⊢ alt₁ ≈ alt'₁,      …,      Γ ⊢ altₙ ≈ alt'ₙ
--        > —————————————————————————————————————————————————————————————————
--        >  Γ ⊢ case e of { alt₁; …; altₙ } ≈ case f of { alt'₁; …; alt'ₙ }
--
--    * Two @if@ expressions are similar if their conditions and branches
--      are similar.
--
--        >  Γ ⊢ e₁ ≈ f₁,       Γ ⊢ e₂ ≈ f₂,       Γ ⊢ e₃ ≈ f₃
--        > ———————————————————————————————————————————————————
--        >  Γ ⊢ if e₁ then e₂ else e₃ ≈ if f₁ then f₂ else f₃
--
--    * All AST nodes which do not contain any variables are similar to
--      themselves under every 'Renaming' @Γ@.
--
--        > ———————————  ———————————————————————————  ———————————————————————
--        >  Γ ⊢ C ≈ C    Γ ⊢ undefined ≈ undefined    Γ ⊢ error s ≈ error s
--
--        Where @C@ is a constructor or integer literal and @s@ is an
--        arbitrary error message.
instance Similar IR.Expr where
  similar' e1 e2 = similarExpr e1 e2
    .&&. similar' (IR.exprTypeSchema e1) (IR.exprTypeSchema e2)

-- | Like 'similar'' for expressions but ignores optional type annotations.
similarExpr :: IR.Expr -> IR.Expr -> Renaming -> Bool
-- Compare variables.
similarExpr (IR.Var _ v1 _) (IR.Var _ v2 _) = similarVars IR.ValueScope v1 v2

-- Bind variables in lambda abstractions.
similarExpr (IR.Lambda _ xs e _) (IR.Lambda _ ys f _) =
  let ns = map IR.varPatQName xs
      ms = map IR.varPatQName ys
  in  similar' e f . extendRenaming IR.ValueScope ns ms .&&. similar' xs ys

-- Recursively compare, applications, visible type applications and @case@ and
-- @if@ expressions.
similarExpr (IR.App _ e1 e2 _) (IR.App _ f1 f2 _) =
  similar' e1 f1 .&&. similar' e2 f2
similarExpr (IR.TypeAppExpr _ e s _) (IR.TypeAppExpr _ f t _) =
  similar' e f .&&. similar' s t
similarExpr (IR.Case _ e as _) (IR.Case _ f bs _) =
  similar' e f .&&. similar' as bs
similarExpr (IR.If _ e1 e2 e3 _) (IR.If _ f1 f2 f3 _) =
  similar' e1 f1 .&&. similar' e2 f2 .&&. similar' e3 f3

-- Expressions without variables are only similar to themselves.
similarExpr (IR.Con _ n1 _         ) (IR.Con _ n2 _       ) = const (n1 == n2)
similarExpr (IR.Undefined _ _      ) (IR.Undefined _ _    ) = const True
similarExpr (IR.ErrorExpr  _ m1 _  ) (IR.ErrorExpr  _ m2 _) = const (m1 == m2)
similarExpr (IR.IntLiteral _ i1 _  ) (IR.IntLiteral _ i2 _) = const (i1 == i2)

-- Combinations of different constructors are not similar.
similarExpr (IR.Var        _ _  _  ) _                      = const False
similarExpr (IR.Lambda      _ _ _ _) _                      = const False
similarExpr (IR.App         _ _ _ _) _                      = const False
similarExpr (IR.TypeAppExpr _ _ _ _) _                      = const False
similarExpr (IR.Case        _ _ _ _) _                      = const False
similarExpr (IR.If _ _ _ _ _       ) _                      = const False
similarExpr (IR.Con _ _ _          ) _                      = const False
similarExpr (IR.Undefined _ _      ) _                      = const False
similarExpr (IR.ErrorExpr  _ _ _   ) _                      = const False
similarExpr (IR.IntLiteral _ _ _   ) _                      = const False

-- | Two alternatives that match the same constructor @C@ are similar
--   if their right-hand sides are similar under an extended 'Renaming'
--   that maps the variable patterns from the first alternative to the
--   corresponding variable patterns from the second alternative.
--   Additionally, the type annotations of their variable patterns must be
--   similar (if there are any).
--
--   >  Γ ∪ { x₁ ↦ y₁, …, xₙ ↦ yₙ } ⊢ e ≈ f, Γ ⊢ p₁ ≈ q₁, …, Γ ⊢ pₙ ≈ qₙ
--   > ——————————————————————————————————————————————————————————————————
--   >             Γ ⊢ C p₁ … pₙ -> e ≈ C q₁ … qₙ -> f
--
--   where @xᵢ@ and @yᵢ@ denote the names of the variables bound by the
--   patterns @pᵢ@ and @qᵢ@ respectively.
instance Similar IR.Alt where
  similar' (IR.Alt _ c xs e) (IR.Alt _ d ys f)
    | c == d
    = let ns = map IR.varPatQName xs
          ms = map IR.varPatQName ys
      in  similar' e f . extendRenaming IR.ValueScope ns ms .&&. similar' xs ys
    | otherwise
    = const False

-- | Two variable patterns are similar if they either both don't have a type
--   annotation or are annotated with similar types.
--
--   >                      Γ ⊢ τ ≈ τ'
--   > ———————————  ——————————————————————————
--   >  Γ ⊢ x ≈ y    Γ ⊢ (x :: τ) ≈ (y :: τ')
instance Similar IR.VarPat where
  similar' (IR.VarPat _ _ t1) (IR.VarPat _ _ t2) = similar' t1 t2

-------------------------------------------------------------------------------
-- Similarity test for declarations                                          --
-------------------------------------------------------------------------------

-- | Two function declarations are similar if their right-hand sides are
--   similar under an extended 'Renaming' that maps the corresponding type
--   arguments and arguments to each other. If the arguments are annotated,
--   their type annotations must be similar under an extended 'Renaming'
--   that maps the corresponding type arguments to each other.
--
--   >  Γ ∪ { α₁ ↦ β₁, …, αₘ ↦ βₘ, x₁ ↦ y₁, …, xₙ ↦ yₙ } ⊢ e ≈ f
--   >  Γ ∪ { α₁ ↦ β₁, …, αₘ ↦ βₘ } ⊢ p₁ ≈ q₁, …,
--   >  Γ ∪ { α₁ ↦ β₁, …, αₘ ↦ βₘ } ⊢ pₙ ≈ qₙ
--   > ——————————————————————————————————————————————————————————
--   >  Γ ⊢ g @α₁ … @αₘ p₁ … pₙ = e ≈ g @β₁ … @βₘ q₁ … qₙ = f
--
--   where @xᵢ@ and @yᵢ@ denote the names of the variables bound by the
--   patterns @pᵢ@ and @qᵢ@ respectively.
--
--   If the function has an explicit return type annotation, the annotated
--   return typed must be similar as well.
--
--   >  Γ ∪ { α₁ ↦ β₁, …, αₘ ↦ βₘ, x₁ ↦ y₁, …, xₙ ↦ yₙ } ⊢ e ≈ f
--   >  Γ ∪ { α₁ ↦ β₁, …, αₘ ↦ βₘ } ⊢ p₁ ≈ q₁, …,
--   >  Γ ∪ { α₁ ↦ β₁, …, αₘ ↦ βₘ } ⊢ pₙ ≈ qₙ,
--   >  Γ ∪ { α₁ ↦ β₁, …, αₘ ↦ βₘ } ⊢ τ ≈ τ',
--   > ——————————————————————————————————————————————————————————
--   >  Γ ⊢ g @α₁ … @αₘ p₁ … pₙ :: τ = e ≈ g @β₁ … @βₘ q₁ … qₙ :: τ' = f
instance Similar IR.FuncDecl where
  similar' (IR.FuncDecl _ g as xs s e) (IR.FuncDecl _ h bs ys t f)
    | IR.declIdentName g == IR.declIdentName h && length as == length bs
    = let as' = map IR.typeVarDeclQName as
          bs' = map IR.typeVarDeclQName bs
          xs' = map IR.varPatQName xs
          ys' = map IR.varPatQName ys
      in  (    similar' e f
          .    extendRenaming IR.ValueScope xs' ys'
          .&&. similar' xs ys
          .&&. similar' s  t
          )
            . extendRenaming IR.TypeScope as' bs'
    | otherwise
    = const False

-- | Two type synonym declarations are similar if their right-hand sides are
--   similar under an extended 'Renaming' that maps the corresponding type
--   arguments to each other.
--
--   >      Γ ∪ { α₁ ↦ β₁, …, αₙ ↦ βₙ } ⊢ τ ≈ τ'
--   > ——————————————————————————————————————————————
--   >  Γ ⊢ type T α₁ … αₙ = τ ≈ type T β₁ … βₙ = τ'
--
--   Two data type declarations are similar if their constructors are pairwise
--   similar under an extended 'Renaming' that maps the corresponding type
--   arguments to each other. Note that the order of the constructors in
--   important.
--
--   >  Γ ∪ { α₁ ↦ β₁, …, αₙ ↦ βₙ } ⊢ con₁ ≈ con'₁, …,
--   >  Γ ∪ { α₁ ↦ β₁, …, αₙ ↦ βₙ } ⊢ conₘ ≈ con'ₘ
--   > ————————————————————————————————————————————————
--   >  Γ ⊢ data D α₁ … αₙ = con₁  | … | conₘ
--   >    ≈ data D β₁ … βₙ = con'₁ | … | con'ₘ
instance Similar IR.TypeDecl where
  similar' (IR.TypeSynDecl _ d1 as t1) (IR.TypeSynDecl _ d2 bs t2)
    | IR.declIdentName d1 == IR.declIdentName d2 && length as == length bs
    = let as' = map IR.typeVarDeclQName as
          bs' = map IR.typeVarDeclQName bs
      in  similar' t1 t2 . extendRenaming IR.TypeScope as' bs'
    | otherwise
    = const False

  similar' (IR.DataDecl _ d1 as cs1) (IR.DataDecl _ d2 bs cs2)
    | IR.declIdentName d1 == IR.declIdentName d2 && length as == length bs
    = let as' = map IR.typeVarDeclQName as
          bs' = map IR.typeVarDeclQName bs
      in  similar' cs1 cs2 . extendRenaming IR.TypeScope as' bs'
    | otherwise
    = const False

  -- Combinations of different constructors are not similar.
  similar' (IR.TypeSynDecl _ _ _ _) _ = const False
  similar' (IR.DataDecl    _ _ _ _) _ = const False

-- | Two constructor declarations are similar if their field types are similar.
--
--   >  Γ ⊢ τ₁ ≈ τ'₁, …, Γ ⊢ τₙ ≈ τ'ₙ
--   > ———————————————————————————————
--   >   Γ ⊢ C τ₁ … τₙ ≈ C τ'₁ … τ'ₙ
instance Similar IR.ConDecl where
  similar' (IR.ConDecl _ c1 ts1) (IR.ConDecl _ c2 ts2)
    | IR.declIdentName c1 == IR.declIdentName c2 = similar' ts1 ts2
    | otherwise = const False
