From Base Require Import Free Handlers.
From Base Require Import Prelude.

From Base Require Import Free.Instance.Comb.
From Base Require Import Free.Instance.Maybe.

(* QuickCheck properties are implemented as Coq propositions. *)
Definition Property (Shape : Type) (Pos : Shape -> Type) := forall (handler : forall (A : Type) (NF : Normalform Shape Pos A),
 Handler Shape Pos A), Prop.


(* * [Testable] type class *)

(* [class Testable prop where property :: prop -> Property] *)
Class Testable (prop : Type) := { 
  property' : prop -> Prop;
  property : prop -> Prop }.

(* [instance Testable Prop] *)
Instance TestableProp
  : Testable Prop
 := { property' p := p;
      property p := p }.

(* [instance Testable Property] *)
Instance TestableProperty (Shape : Type) (Pos : Shape -> Type)
  : Testable (Property Shape Pos)
 := { property' p := forall (handler : forall (A : Type) (NF : Normalform Shape Pos A),
                             Handler Shape Pos A), p handler;
      property p := p (NoHandler Shape Pos) }.

(* [instance Testable Bool] *)
Instance TestableBool
  : Testable bool
 := { property' b := b = true;
      property b := b = true }.

(* [instance Testable b => Testable (a -> b)] *)
Instance TestableFunction (A : Type) (B : Type) (T_B : Testable B)
  : Testable (A -> B)
 := { property' f := forall x, property' (f x);
      property f := forall x, property (f x) }.

(* Helper instance for dependent types.
   This allows us to use [quickCheck] both for proving properties for specific
   and for arbitrary effects by providing a default strategy for how the
   binders for [Shape] and [Pos] can be converted to properties. *)
Instance TestableForall
  (A : Type) (B : A -> Type) (T_Bx : forall x, Testable (B x))
  : Testable (forall x, B x)
 := { property' f := forall x, property' (f x);
      property f := forall x, property (f x); }.

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
                      end;
      property fp := match fp with
                      | pure p     => property p
                      | impure _ _ => False
                      end }.

(* Similar to Testable, but returns a Property instead of a Prop so
   that a handler can be applied. *)
Class Handleable (Shape : Type) (Pos : Shape -> Type) (prop : Type) := 
  {  toProperty : prop -> Property Shape Pos
}.

Instance HandleableProperty (Shape : Type) (Pos : Shape -> Type) : Handleable Shape Pos (Property Shape Pos) := {
  toProperty p := p
}.

Instance HandleableFree (Shape : Type) (Pos : Shape -> Type) {A : Type} {H_A : Handleable Shape Pos A} : Handleable Shape Pos (Free Shape Pos A) := {
  toProperty fp := match fp with
                   | pure p => toProperty p
                   | impure s pf => (fun _ => False)
                   end }.

Instance HandleableFunction (Shape : Type) (Pos : Shape -> Type) (A : Type) (B : Type) 
 (T_B : Handleable Shape Pos B)
  : Handleable Shape Pos (A -> B)
 := { toProperty f := fun handler => forall x, toProperty (f x) handler }.

Instance HandleableForall (Shape : Type) (Pos : Shape -> Type)
  (A : Type) (B : A -> Type) (T_Bx : forall x, Handleable Shape Pos (B x))
  : Handleable Shape Pos (forall x, B x)
 := { toProperty f := fun handler => forall x, toProperty (f x) handler }.


(* [quickCheck :: Testable a => a -> IO ()]
   In Haskell this function is used to test a QuickCheck property.
   We are reusing the name to convert the computation of a quickCheck
   property to a Coq property that can actually be proven. *)
Definition quickCheck {A : Type} {T_A : Testable A} (x : A) : Prop
 := property x.

(* Like quickCheck, but with a concrete handler as an additional argument.
   The property's Shape and Pos arguments must be inferred or match
   the effect stack determined by the handler. *)
Definition quickCheckHandle {Shape : Type} {Pos : Shape -> Type} {A : Type} `{Handleable Shape Pos A}
 (x : A) handler : Prop := (toProperty x) handler.

(* Like quickCheck, but with a universally quantified handler.
   Proving an equality with a universally quantified handler is
   equivalent to proving the same equality without the handler.
   Proving an inequality is impossible as there is no information
   about the return value or even return type of the handler.

   As long as there are no properties associated with the Handler
   class, it is not advised to use this function. *)
Definition quickCheckQuantifyHandler {A : Type} {T_A : Testable A} (x : A) : Prop
 := property' x.

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
   := pure (fun handler => property' fb).

  (* [(==>) :: Bool -> Property -> Property] *)
  Definition preProp (fb : Free' Bool') (p : Free' Property')
    : Free' Property'
   := pure (fun handler => property fb -> property p).

  (* [(===) :: a -> a -> Property] *)
  Definition eqProp (A : Type) `(NF : Normalform Shape Pos A)
    (fx : Free' A) (fy : Free' A)
    : Free' Property'
   := pure (fun handler => 
             @handle Shape Pos A (handler A NF) fx = handle fy).

  (* [(=/=) :: a -> a -> Property] *)
  Definition neqProp (A : Type) `(NF : Normalform Shape Pos A) 
                     (fx : Free' A) (fy : Free' A)
    : Free' Property'
   := pure (fun handler => 
             @handle Shape Pos A (handler A NF) fx <> handle fy).

  (* [(.&&.) :: Property -> Property -> Property] *)
  Definition conjProp (fp1 : Free' Property') (fp2 : Free' Property')
    : Free' Property'
   :=  fp1 >>= fun p1 => 
       fp2 >>= fun p2 => 
       pure (fun handler => property (p1 handler) /\ property (p2 handler)).

  (* [(.||.) :: Property -> Property -> Property] *)
  Definition disjProp (fp1 : Free' Property') (fp2 : Free' Property')
    : Free' Property'
   :=  fp1 >>= fun p1 => 
       fp2 >>= fun p2 => 
       pure (fun handler => property (p1 handler) \/ property (p2 handler)).
End SecQuickCheck.

(* Helper lemma to avoid the [match] expression introduced by [property]. *)
Lemma pure_bool_property:
  forall (Shape : Type)
         (Pos : Shape -> Type)
         (fb : Free Shape Pos (Bool Shape Pos)),
  property fb <-> fb = True_ Shape Pos.
Proof.
  simpl. intros Shape Pos fb. split; intros H.
  - (* -> *) destruct fb as [b |].
    + (* fb = pure b *) rewrite H. reflexivity.
    + (* fb = impure _ _ *) contradiction H.
  - (* <- *) rewrite H. reflexivity.
Qed.
