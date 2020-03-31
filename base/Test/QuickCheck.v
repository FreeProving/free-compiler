From Base Require Import Free.
From Base Require Import Prelude.

(* QuickCheck properties are implemented as Coq propositions. *)
Definition Property (Shape : Type) (Pos : Shape -> Type) := Prop.

(* * [Testable] type class *)

(* [class Testable prop where property :: prop -> Property] *)
Class Testable (prop : Type) := { property' : prop -> Prop }.

(* [instance Testable Property] *)
Instance TestableProperty
  : Testable Prop
 := { property' p := p }.

(* [instance Testable Bool] *)
Instance TestableBool
  : Testable bool
 := { property' b := b = true }.

(* [instance Testable b => Testable (a -> b)] *)
Instance TestableFunction (A : Type) (B : Type) (T_B : Testable B)
  : Testable (A -> B)
 := { property' f := forall x, property' (f x) }.

(* Helper instance for dependent types.
   This allows us to use [quickCheck] both for proving properties for specific
   and for arbitrary effects by providing a default strategy for how the
   binders for [Shape] and [Pos] can be converted to properties. *)
Instance TestableForall
  (A : Type) (B : A -> Type) (T_Bx : forall x, Testable (B x))
  : Testable (forall x, B x)
 := { property' f := forall x, property' (f x) }.

(* Helper instance for monadically lifted values.

   This instance defines the strategy for how to handle the computation of
   a Coq property by a QuickCheck property defined in Haskell.
   Here we say that a property must produce a [pure] value, otherwise it does
   not hold. In case of the effect of partiality, this means that the
   QuickCheck property [prop_undefined = undefined] is not satisfied.
   (Note that due to the non-strict definition of [(===)] the property
   [prop_undefined_eq = undefined === undefined] would still be true)

   Whether this strategy makes sense in case of other effects such as
   non-determinism still has to be investigated. For example, does the
   property [prop_true_or_false = True ? False] hold or not? With the
   current implementation it does not hold since the choice operator
   produces an [impure] value.
   *)
Instance TestableFree (Shape : Type) (Pos : Shape -> Type)
                      (A : Type) (T_A : Testable A)
  : Testable (Free Shape Pos A)
 := { property' fp := match fp with
                      | pure p     => property' p
                      | impure _ _ => False
                      end }.

(* [property :: Bool -> Property]
   Since we do not support type classes is Haskell, only the [Testable] type
   class instance for [Bool] is accessable from Haskell. *)
Definition property (Shape : Type) (Pos : Shape -> Type)
                    (fb : Free Shape Pos (Bool Shape Pos))
  : Free Shape Pos (Property Shape Pos)
 := pure (property' fb).

(* [quickCheck :: Testable a => a -> IO ()]
   In Haskell this function is used to test a QuickCheck property.
   We are reusing the name to convert the computation of a quickCheck
   property to a Coq property that can actually be proven. *)
Definition quickCheck {A : Type} {T_A : Testable A} (x : A) : Prop
 := property' x.

(* * Constructing QuickCheck Properties *)
Section SecQuickCheck.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).
  Notation "'Property''" := (Property Shape Pos).
  Notation "'Bool''" := (Bool Shape Pos).

  (* [(==>) :: Bool -> Property -> Property] *)
  Definition preProp (b : Free' Bool') (p : Free' Property')
    : Free' Property'
   := pure (property' b -> property' p).

  (* [(===) :: a -> a -> Property] *)
  Definition eqProp (A : Type) (x : Free' A) (y : Free' A)
    : Free' Property'
   := pure (x = y).

  (* [(=/=) :: a -> a -> Property] *)
  Definition neqProp (A : Type) (x : Free' A) (y : Free' A)
    : Free' Property'
   := pure (x <> y).

  (* [(.&&.) :: Property -> Property -> Property] *)
  Definition conjProp (p1 : Free' Property') (p2 : Free' Property')
    : Free' Property'
   := pure (property' p1 /\ property' p2).

  (* [(.||.) :: Property -> Property -> Property] *)
  Definition disjProp (p1 : Free' Property') (p2 : Free' Property')
    : Free' Property'
   := pure (property' p1 \/ property' p2).

End SecQuickCheck.

(* Helper lemma to avoid the [match] expression introduced by [property']. *)
Lemma pure_bool_property :
  forall (Shape : Type)
         (Pos : Shape -> Type)
         (fb : Free Shape Pos (Bool Shape Pos)),
  property' fb <-> fb = True_ Shape Pos.
Proof.
  simpl. intros Shape Pos fb. split; intros H.
  - (* -> *) destruct fb as [b |].
    + (* fb = pure b *) rewrite H. reflexivity.
    + (* fb = impure _ _ *) contradiction H.
  - (* <- *) rewrite H. reflexivity.
Qed.
