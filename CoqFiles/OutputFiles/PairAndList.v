Add LoadPath "../ImportedFiles". 
 Require Import String.
 Require Import ImportModules.
 Import Monad.
 Module Test.
Set Implicit Arguments.
Set Maximal Implicit Insertion. 
 
Definition identP (ox : option (Pair nat nat)) : option (Pair nat nat) :=
  ox >>=
  (fun (x : Pair nat nat) => match x with | P l r => return_ (P l r) end). 
 
Definition switch (a b : Type) (ox : option (Pair a b)) : option (Pair b a) :=
  ox >>= (fun (x : Pair a b) => match x with | P a b => return_ (P b a) end). 
 
Fixpoint identL (fuel : nat) (oxs : option (List nat)) : option (List nat)
           := match fuel with
              | O => None
              | S rFuel =>
                  oxs >>=
                  (fun (xs : List nat) =>
                     match xs with
                     | Nil => return_ Nil
                     | Cons x xs => return_ (Cons x (identL rFuel xs))
                     end)
              end. 
 
End Test.
 