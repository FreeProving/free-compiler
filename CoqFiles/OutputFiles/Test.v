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
 
Definition plus (oa : option nat) (ob : option nat) : option nat :=
  oa >>= (fun (a : nat) => ob >>= (fun (b : nat) => return_ (a + b))). 
 
Definition minus (oa : option nat) (ob : option nat) : option nat :=
  oa >>= (fun (a : nat) => ob >>= (fun (b : nat) => return_ (a - b))). 
 
Definition not (ob : option bool) : option bool :=
  ob >>=
  (fun (b : bool) =>
     match b with
     | false => return_ true
     | true => return_ false
     end). 
 
Definition null (a : Type) (olist : option (List a)) : option bool :=
  olist >>=
  (fun (list : List a) =>
     match list with
     | Nil => return_ true
     | _ => return_ false
     end). 
 
Fixpoint append' (a : Type) (xs : List a) (oys : option (List a)) : option (List
                                                                            a)
           := match xs with
              | Nil => oys
              | Cons z ozs => return_ (Cons z (ozs >>= (fun zs => append' zs oys)))
              end. 
 
Definition append (a : Type) (oxs : option (List a)) (oys : option (List a))
   : option (List a) :=
  oxs >>= (fun (xs : List a) => append' xs oys). 
 
Fixpoint reverse_' (a : Type) (xs : List a) : option (List a)
           := match xs with
              | Nil => return_ Nil
              | Cons y oys => append (oys >>= (fun ys => reverse_' ys)) (singleton y)
              end. 
 
Definition reverse_ (a : Type) (oxs : option (List a)) : option (List a) :=
  oxs >>= (fun (xs : List a) => reverse_' xs). 
 
Fixpoint concat_' (a : Type) (xs : List (List a)) : option (List a)
           := match xs with
              | Nil => return_ Nil
              | Cons y oys => append y (oys >>= (fun ys => concat_' ys))
              end. 
 
Definition concat_ (a : Type) (oxs : option (List (List a)))
   : option (List a) :=
  oxs >>= (fun (xs : List (List a)) => concat_' xs). 
 
Fixpoint length'' (a : Type) (xs : List a) : option nat
           := match xs with
              | Nil => return_ 0
              | Cons y oys => plus (return_ 1) (oys >>= (fun ys => length'' ys))
              end. 
 
Definition length' (a : Type) (oxs : option (List a)) : option nat :=
  oxs >>= (fun (xs : List a) => length'' xs). 
 
Definition indexLength (a : Type) (oxs : option (List a)) : option nat :=
  oxs >>= (fun (xs : List a) => minus (length' (return_ xs)) (return_ 1)). 
 
End Test.
 