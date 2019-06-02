From Base Require Import Prelude.
From Base Require Import Free.

(*
  head :: [a] -> a
  head xs = case xs of
    []      -> undefined
    x : xs' -> x
*)

Definition head
    {F : Type -> Type} {P__F : Partial F}
    {a : Type} (xs : Free C__F (List C__F a)) : Free C__F a :=
  xs >>= fun(xs0 : List C__F a) =>
    match xs0 with
    | Nil       => undefined
    | Cons x xs => x
    end.
