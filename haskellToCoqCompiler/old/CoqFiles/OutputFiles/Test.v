Add LoadPath "../ImportedFiles". 
 Require Import String.
 Require Import ImportModules.
 Import Monad.
 Module Test.
Set Implicit Arguments.
Set Maximal Implicit Insertion. 
 
Inductive Boolean : Type := B_True : Boolean |  B_False : Boolean. 
 
Inductive Maybe (a : Type) : Type
  := Nothing : Maybe a
  |  Just : option a -> Maybe a. 
 
Arguments Nothing {a}. 
 
Inductive Either (a : Type) (b : Type) : Type
  := Left : option a -> Either a b
  |  Right : option b -> Either a b. 
 
Inductive Tree (a : Type) : Type
  := Leaf : Tree a
  |  Branch : option a -> option (Tree a) -> option (Tree a) -> Tree a. 
 
Arguments Leaf {a}. 
 
Inductive Test : Type
  := T1 : option nat -> Test
  |  T2 : option string -> Test. 
 
Definition plus (fuel : nat) (oa : option nat) (ob : option nat) : option nat :=
  oa >>= (fun (a : nat) => ob >>= (fun (b : nat) => return_ (a + b))). 
 
Definition minus (fuel : nat) (oa : option nat) (ob : option nat)
   : option nat :=
  oa >>= (fun (a : nat) => ob >>= (fun (b : nat) => return_ (a - b))). 
 
Definition not (fuel : nat) (ob : option bool) : option bool :=
  ob >>=
  (fun (b : bool) =>
     match b with
     | false => return_ true
     | true => return_ false
     end). 
 
Definition null (fuel : nat) (a : Type) (olist : option (List a))
   : option bool :=
  olist >>=
  (fun (list : List a) =>
     match list with
     | Nil => return_ true
     | _ => return_ false
     end). 
 
Fixpoint append (fuel : nat) (a : Type) (oxs : option (List a)) (oys
                  : option (List a)) : option (List a) :=
           match fuel with
           | O => None
           | S rFuel =>
               oxs >>=
               (fun (xs : List a) =>
                  oys >>=
                  (fun (ys : List a) =>
                     match xs with
                     | Nil => return_ ys
                     | Cons z zs => return_ (Cons z (append rFuel zs (return_ ys)))
                     end))
           end. 
 
Fixpoint reverse_ (fuel : nat) (a : Type) (oxs : option (List a)) : option (List
                                                                            a) :=
           match fuel with
           | O => None
           | S rFuel =>
               oxs >>=
               (fun (xs : List a) =>
                  match xs with
                  | Nil => return_ Nil
                  | Cons y ys => append rFuel (reverse_ rFuel ys) (singleton y)
                  end)
           end. 
 
Fixpoint concat_ (fuel : nat) (a : Type) (oxs : option (List (List a))) : option
                                                                          (List a) :=
           match fuel with
           | O => None
           | S rFuel =>
               oxs >>=
               (fun (xs : List (List a)) =>
                  match xs with
                  | Nil => return_ Nil
                  | Cons y ys => append rFuel y (concat_ rFuel ys)
                  end)
           end. 
 
Fixpoint length' (fuel : nat) (a : Type) (oxs : option (List a)) : option nat :=
           match fuel with
           | O => None
           | S rFuel =>
               oxs >>=
               (fun (xs : List a) =>
                  match xs with
                  | Nil => return_ 0
                  | Cons y ys => plus rFuel (return_ 1) (length' rFuel ys)
                  end)
           end. 
 
Definition indexLength (fuel : nat) (a : Type) (oxs : option (List a))
   : option nat :=
  oxs >>=
  (fun (xs : List a) => minus fuel (length' fuel (return_ xs)) (return_ 1)). 
 
End Test.
 