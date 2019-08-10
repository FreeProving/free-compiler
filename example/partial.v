From Base Require Import Prelude.
From Base Require Import Free.

(*
  head :: [a] -> a
  head xs = case xs of
    []      -> undefined
    x : xs' -> x
*)

Definition head
    (Shape : Type) (Pos : Shape -> Type) (P : Partial Shape Pos)
    {a : Type} (xs : Free Shape Pos (List Shape Pos a)) : Free Shape Pos a :=
  xs >>= fun(xs0 : List Shape Pos a) =>
    match xs0 with
    | nil       => undefined
    | cons x xs => x
    end.
