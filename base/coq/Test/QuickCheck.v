From Base Require Import Free Handlers.
From Base Require Import Prelude.

From Base Require Import Free.Instance.Comb.
From Base Require Import Free.Instance.Maybe.

(* QuickCheck properties are implemented as Coq propositions
   that are parameterized over a handler. The handler is used
   when comparing values with [(===)] and [(=/=)]. *)
Definition Property (Shape : Type) (Pos : Shape -> Type) : Type
 := (forall (A : Type), Handler Shape Pos A) -> Prop.

(* [ShareableArgs] instance for [Property]. *)
Instance ShareableArgsProperty (Shape : Type) (Pos : Shape -> Type)
  : ShareableArgs Shape Pos (Property Shape Pos) := {
    shareArgs _ := pure
}.

(* * [Testable] type class *)

(* [class Testable prop where property :: prop -> Property] *)
Class Testable (Shape : Type) (Pos : Shape -> Type) (prop : Type) := {
  property : prop -> Property Shape Pos
}.

(* [instance Testable Property] *)
Instance TestableProperty (Shape : Type) (Pos : Shape -> Type)
  : Testable Shape Pos (Property Shape Pos)
 := { property p := p }.

(* [instance Testable Bool] *)
Instance TestableBool (Shape : Type) (Pos : Shape -> Type)
  : Testable Shape Pos (Bool Shape Pos)
 := { property b _ := b = true }.

(* [instance Testable b => Testable (a -> b)] *)
Instance TestableFunction
  (Shape : Type) (Pos : Shape -> Type)
  (A : Type) (B : Type) (T_B : Testable Shape Pos B)
  : Testable Shape Pos (A -> B)
 := { property f handler := forall x, property (f x) handler }.

(* Helper instance for dependent types.
   This allows us to use [quickCheck] both for proving properties for specific
   and for arbitrary effects by providing a default strategy for how the
   binders for [Shape] and [Pos] can be converted to properties. *)
Instance TestableForall
  (Shape : Type) (Pos : Shape -> Type)
  (A : Type) (B : A -> Type) (T_Bx : forall x, Testable Shape Pos (B x))
  : Testable Shape Pos (forall x, B x)
 := { property f handler := forall x, property (f x) handler }.

(* Helper instance for monadically lifted values. *)
Instance TestableFree (Shape : Type) (Pos : Shape -> Type)
                      (A : Type) (T_A : Testable Shape Pos A)
  : Testable Shape Pos (Free Shape Pos A)
 := { property fp handler := match fp with
                             | pure p => property p handler
                             | impure s pf => False
                             end }.

(* [quickCheck :: Testable a => a -> IO ()]

   In Haskell this function is used to test a QuickCheck property.
   We are reusing the name to convert the computation of a QuickCheck
   property to a Coq property that can actually be proven. *)
Definition quickCheck
  {A    : forall Shape Pos, Type}
  {T_A  : forall Shape Pos, Testable Shape Pos (A Shape Pos)}
  (prop : forall Shape Pos, A Shape Pos)
  : Prop
 := forall Shape Pos, property (prop Shape Pos) (NoHandler Shape Pos).

(* Like [quickCheck] but with additional arguments for the [Shape] and
   [Pos]ition.

   You should use this function than [Shape] and [Pos] have been introduced
   by an explicit [forall] already, e.g., because there are preconditions
   that cannot be formulated in Haskell. *)
Definition quickCheck'
   {Shape : Type} {Pos : Shape -> Type}
   {A : Type} {T_A : Testable Shape Pos A}
   (prop : A)
   : Prop
 := property prop (NoHandler Shape Pos).

(* Like [quickCheck] but with a concrete handler as an additional argument.
   The property's [Shape] and [Pos] arguments must be inferred or match
   the effect stack determined by the handler. *)
Definition quickCheckHandle
  {Shape} {Pos : Shape -> Type}
  {A : Type} {T_A : Testable Shape Pos A}
  (prop : A)
  (handler : forall (A : Type), Handler Shape Pos A)
  : Prop
 := property prop handler.

(* Utility function to specify the evaluation strategy of a property without
   having to bind the [Shape] and [Pos] explicitly.

   This function is used as follows:
   [quickCheck (withStrategy Cbn prop_foo)].
 *)
Definition withStrategy
  {A    : forall Shape Pos, Type}
  (S    : forall Shape Pos, Strategy Shape Pos)
  (prop : forall Shape Pos (S : Strategy Shape Pos), A Shape Pos)
  (Shape : Type) (Pos : Shape -> Type)
  : A Shape Pos
 := prop Shape Pos (S Shape Pos).

(* * Constructing QuickCheck Properties *)
Section SecQuickCheck.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).
  Notation "'Property''" := (Property Shape Pos).
  Notation "'Bool''" := (Bool Shape Pos).

  (* [property :: Bool -> Property]
     Since we do not support type classes is Haskell, only the [Testable] type
     class instance for [Bool] is accessable from Haskell. *)
  Definition boolProp (fb : Free' Bool')
    : Free' Property'
   := pure (fun handler => property fb handler).

  (* [(==>) :: Bool -> Property -> Property] *)
  Definition preProp (fb : Free' Bool') (fp : Free' Property')
    : Free' Property'
   := pure (fun handler => property fb handler -> property fp handler).

  (* Version of [preProp] that allows arbitrary preconditions. *)
  Definition preProp' (fx : Free' Property') (fy : Free' Property')
    : Free' Property'
   := pure (fun handler => property fx handler -> property fy handler).

  (* [(===) :: a -> a -> Property] *)
  Definition eqProp (A : Type) `{Normalform Shape Pos A} (fx : Free' A) (fy : Free' A)
    : Free' Property'
   := pure (fun handler => handle fx = handle fy).

  (* [(=/=) :: a -> a -> Property] *)
  Definition neqProp (A : Type) `{Normalform Shape Pos A} (fx : Free' A) (fy : Free' A)
    : Free' Property'
   := pure (fun handler => handle fx <> handle fy).

  (* [(.&&.) :: Property -> Property -> Property] *)
  Definition conjProp (fp1 : Free' Property') (fp2 : Free' Property')
    : Free' Property'
   := fp1 >>= fun p1 =>
      fp2 >>= fun p2 =>
      pure (fun handler => p1 handler /\ p2 handler).

  (* [(.||.) :: Property -> Property -> Property] *)
  Definition disjProp (fp1 : Free' Property') (fp2 : Free' Property')
    : Free' Property'
   := fp1 >>= fun p1 =>
      fp2 >>= fun p2 =>
      pure (fun handler => p1 handler \/ p2 handler).
End SecQuickCheck.

(* Helper lemma to avoid the [match] expression introduced by [property]. *)
Lemma pure_bool_property:
  forall (Shape : Type)
         (Pos : Shape -> Type)
         (fb : Free Shape Pos (Bool Shape Pos))
         (handler : forall (A : Type), Handler Shape Pos A),
  property fb handler <-> fb = True_ Shape Pos.
Proof.
  simpl. intros Shape Pos fb. split; intros H.
  - (* -> *) destruct fb as [b |].
    + (* fb = pure b *) rewrite H. reflexivity.
    + (* fb = impure _ _ *) contradiction H.
  - (* <- *) rewrite H. reflexivity.
Qed.
