Module Monad.
Set Implicit Arguments.
Set Maximal Implicit Insertion.

Class Monad (m: Type -> Type) := {
  return_ : forall a, a -> m a;
  bind : forall a , m a -> forall b, (a -> m b) -> m b
}.




Instance Maybe : Monad option :={
    return_ := fun a => Some;
    bind := fun a m b f => 
              match m with
              |Some a => f a
              |None  => None 
              end   
}.

Notation "m >>= f" := (bind m _ f) (at level 50, left associativity).

Definition plus (a b : option nat) : option nat :=
  b >>= fun b => 
    a >>= fun a => 
      return_ (a + b).

Definition not (b : option bool) : option bool :=
  b >>= (fun b => match b with 
                 | false => return_ true
                 | true => return_ false
                 end).


End Monad.