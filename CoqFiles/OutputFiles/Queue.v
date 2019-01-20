Add LoadPath "../ImportedFiles". 
 Require Import String.
 Require Import ImportModules.
 Import Monad.
 Module Queue.
Set Implicit Arguments.
Set Maximal Implicit Insertion. 
 
Inductive List (a : Type) : Type
  := Nil : List a
  |  Cons : option a -> option (List a) -> List a. 
 
Arguments Nil {a}. 
 
Definition Queue (a : Type) :=
  List a. 
 
Definition null' (a : Type) (olist : option (List a)) : option bool :=
  olist >>=
  (fun (list : List a) =>
     match list with
     | Nil => return_ (true)
     | Cons _ _ => return_ (false)
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
 
Definition singleton (a : Type) (ox : option a) : option (List a) :=
  ox >>= (fun (x : a) => return_ (Cons (return_ (x)) (return_ (Nil)))). 
 
Definition empty :=
  Nil. 
 
Definition isEmpty (a : Type) (oq : option (Queue a)) : option bool :=
  oq >>= (fun (q : Queue a) => null' (return_ (q))). 
 
Definition front (a : Type) (oq : option (Queue a)) : option a :=
  oq >>= (fun (q : Queue a) => match q with | Cons x _ => x | _ => None end). 
 
Definition add (a : Type) (ox : option a) (oq : option (Queue a))
   : option (Queue a) :=
  ox >>=
  (fun (x : a) =>
     oq >>=
     (fun (q : Queue a) => append (return_ (q)) (singleton (return_ (x))))). 
 
End Queue.
 