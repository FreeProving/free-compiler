Module Monad.
Set Implicit Arguments.
Set Maximal Implicit Insertion.



Definition return_ (A : Type) : A -> option A :=
 Some.

Definition bind (A B : Type) (m : option A) (f : A -> option B) : option B := 
  match m with 
  | Some A => f A
  | None => None 
  end.

Notation "m >>= f" := (bind m f) (left associativity, at level 50).

Check bind.
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

Definition singleton (a : Type) (x : option a)  : option (List a) := 
    return_ (Cons x (return_ Nil)).



Definition null (a : Type) (olist : option (List a)) : option bool :=
     olist >>= fun list =>
                        match list with
                        | Nil => return_ true
                        | Cons _ _ => return_ false
                        end.

(* Händisch transformierte Funktionen (mit Hilfsfunktion) *)
Fixpoint append'' (a : Type) (xs : List a) (oys : option (List a)) : option (List a) :=
  match xs with
  | Nil => oys
  | Cons z ozs => return_ (Cons z (ozs >>= (fun zs => append'' zs oys)))
  end.

Fixpoint append' (a : Type) (oxs oys : option (List a)) : option (List a) :=
  oxs >>= fun xs => append'' xs oys.


Fixpoint reverse'' (a : Type) (xs : List a) : option (List a) :=
  match xs with
  | Nil => return_ Nil
  | Cons y ys => append' (ys >>= reverse'') (singleton y)
  end.

Fixpoint reverse' (a:Type) (oxs : option (List a)) : option (List a) :=
  oxs >>= fun xs => reverse'' xs.

Fixpoint concat'' (a:Type) (xs : List (List a)) : option (List a) :=
  match xs with
  | Nil => return_ Nil
  | Cons y ys => append' y ( ys >>= concat'') 
  end. 

Fixpoint concat' (a : Type) (oxs : option (List (List a))) : option (List a) :=
  oxs >>= fun xs => concat'' xs.




(* Händisch transformierte Funktionen (mit fuel Argument) *)
Fixpoint append (a : Type) (fuel : nat) (oxs oys : option (List a)) : option (List a):=
    match fuel with
    |O => None
    |S (rFuel) => oxs >>= fun xs =>
                    oys >>= fun ys =>  match xs with
                                       | Nil => return_ ys
                                       | Cons z zs => return_ (Cons z (append rFuel zs oys))
                                       end
    end.

Fixpoint reverse (a : Type) (fuel : nat) (oxs : option (List a)) : (option (List a)) :=
    match fuel with
    | O => None 
    | S (rFuel) => oxs >>= fun xs => match xs with
                                     | Nil => return_ Nil 
                                     | Cons y ys => append rFuel (reverse rFuel ys) (singleton y) 
                                     end
    end.

Fixpoint concat (a : Type) (fuel : nat) ( oxs : option (List (List a))) : option (List a) := 
    match fuel with
    | O => None 
    | S (rFuel) => oxs >>= fun xs => match xs with 
                                     | Nil => return_ Nil 
                                     | Cons z zs => append rFuel z (concat rFuel zs)
                                     end
    end.
End Monad.
