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
 
Inductive Pair (a : Type) (b : Type) : Type
  := P : option a -> option b -> Pair a b. 
 
Definition Queue (a : Type) :=
  List a. 
 
Definition Queuel (a : Type) :=
  Pair (List a) (List a). 
 
Definition null' (a : Type) (olist : option (List a)) : option bool :=
  olist >>=
  (fun (list : List a) =>
     match list with
     | Nil => return_ true
     | Cons _ _ => return_ false
     end). 
 
Fixpoint append (fuel : nat) (a : Type) (oxs : option (List a)) (oys
                  : option (List a)) : option (List a)
           := match fuel with
              | O => None
              | S rFuel =>
                  oxs >>=
                  (fun (xs : List a) =>
                     oys >>=
                     (fun (ys : List a) =>
                        match xs with
                        | Nil => return_ ys
                        | Cons z zs => (return_ (Cons z (append rFuel zs (return_ ys))))
                        end))
              end. 
 
Definition singleton (a : Type) (ox : option a) : option (List a) :=
  ox >>= (fun (x : a) => return_ (Cons (return_ x) (return_ Nil))). 
 
Fixpoint reverse' (fuel : nat) (a : Type) (oxs : option (List a)) : option (List
                                                                            a)
           := match fuel with
              | O => None
              | S rFuel =>
                  oxs >>=
                  (fun (xs : List a) =>
                     match xs with
                     | Nil => return_ Nil
                     | Cons y ys => append rFuel (reverse' rFuel ys) (singleton y)
                     end)
              end. 
 
Definition empty (a : Type) : option (Queue a) :=
  return_ Nil. 
 
Definition isEmpty (a : Type) (oq : option (Queue a)) : option bool :=
  oq >>= (fun (q : Queue a) => null' (return_ q)). 
 
Definition front (a : Type) (oq : option (Queue a)) : option a :=
  oq >>= (fun (q : Queue a) => match q with | Cons x _ => x | _ => None end). 
 
Definition add (fuel : nat) (a : Type) (ox : option a) (oq : option (Queue a))
   : option (Queue a) :=
  ox >>=
  (fun (x : a) =>
     oq >>=
     (fun (q : Queue a) => append fuel (return_ q) (singleton (return_ x)))). 
 
Definition emptyl (a : Type) : option (Queuel a) :=
  return_ (P (return_ Nil) (return_ Nil)). 
 
Definition isEmptyl (a : Type) (ox : option (Queuel a)) : option bool :=
  ox >>= (fun (x : Queuel a) => match x with | P f b => null' f end). 
 
Definition frontl (a : Type) (oq : option (Queuel a)) : option a :=
  oq >>=
  (fun (q : Queuel a) =>
     match q with
     | P f b => f >>= (fun f' => match f' with | Cons x xs => x | _ => None end)
     end). 
 
Definition flipQ (fuel : nat) (a : Type) (oq : option (Queuel a))
   : option (Queuel a) :=
  oq >>=
  (fun (q : Queuel a) =>
     match q with
     | P f b =>
         f >>=
         (fun f' =>
            match f' with
            | Nil => return_ (P (reverse' fuel b) (return_ Nil))
            | _ => return_ q
            | _ => None
            end)
     end). 
 
Definition addl (a : Type) (ox : option a) (oq : option (Queuel a))
   : option (Queuel a) :=
  ox >>=
  (fun (x : a) =>
     oq >>=
     (fun (q : Queuel a) =>
        match q with
        | P f b => flipQ (return_ (P f (return_ (Cons (return_ x) b))))
        end)). 
 
End Queue.
 