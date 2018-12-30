Module Monad.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Class Monad (m : Type -> Type) := {
  return_ : forall a, a -> m a;
  bind : forall a , m a -> (forall b, (a -> m b) -> m b)
}.



Notation "m >>= f" := (bind m _ f ) (left associativity, at level 50).


Instance Maybe : Monad option :={
    return_ := fun x => Some;
    bind := fun a m b f =>
              match m with
              |Some a => f a
              |None  => None
              end
}.

Definition plus (a b : option nat) : option nat :=
 a >>= fun x =>
   b >>= fun y => return_ (x + y).

Definition not (b : option bool) :=
  b >>= fun x => match x with
                 | false => return_ true
                 | true => return_ false
                 end.

Inductive Bool : Type :=
    | True : Bool
    | False : Bool.

Inductive May (a : Type) :=
    | Nothing : May a
    | Just : option a -> May a.

Arguments Nothing {a}.

Inductive Either (a b : Type) : Type :=
    | Left : option a -> Either a b
    | Right : option b -> Either a b.

Inductive List (a : Type) :Type :=
    | Nil : List a
    | Cons : option a -> option (List a) -> List a.

Arguments Nil {a}.

Definition null (a : Type) (olist : option (List a)) : option bool :=
     olist >>= fun list =>
                        match list with
                        | Nil => return_ true
                        | Cons _ _ => return_ false
                        end.

Check bind.


Fixpoint append' (a : Type) (xs : List a) (oys : option (List a)) : option (List a) :=
  match xs with
  | Nil => oys
  | Cons z ozs => return_ (Cons z (bind ozs _ (fun zs => append' zs oys)))
  end.

Fixpoint append (a : Type) (oxs oys : option (List a)) : option (List a) :=
  oxs >>= fun xs => append' xs oys.



Fixpoint append'' (a : Type) (fuel : nat) (oxs oys : option (List a)) : option (List a):=
    oxs >>= fun xs =>
      oys >>= fun ys => return_ match xs with
                     |Nil => ys
                     |Cons z zs => match fuel with
                                   | O => ys
                                   | S (rFuel) => Cons z (append' rFuel zs oys)
                                   end
                     end.
End Monad.
