From Base Require Import Prelude.
From Base Require Import Free.

(*

  zip :: [a] -> [b] -> [(a, b)]
  zip xs ys = case xs of
    []      -> []
    x : xs' -> case ys of
      []      -> []
      y : ys' -> (x, y) : (zip xs' ys')

*)

Fixpoint zip'
  (Shape : Type) (Pos : Shape -> Type)
  {a b : Type} (xs : List Shape Pos a) (ys : Free Shape Pos (List Shape Pos b))
  : Free Shape Pos (List Shape Pos (Pair Shape Pos a b)) :=
  match xs with
  | nil        => Nil
  | cons x xs' =>
      ys >>= fun(ys0 : List Shape Pos b) =>
        match ys0 with
        | nil        => Nil
        | cons y ys' =>
            Cons (Pair_ x y) (
              xs' >>= fun(xs'0 : List Shape Pos a) => zip' Shape Pos xs'0 ys'
            )
        end
  end.

Definition zip
  (Shape : Type) (Pos : Shape -> Type)
  {a b : Type} (xs : Free Shape Pos (List Shape Pos a)) 
  (ys : Free Shape Pos (List Shape Pos b)) 
  : Free Shape Pos (List Shape Pos (Pair Shape Pos a b)) :=
  xs >>= fun(xs0 : List Shape Pos a) =>
    zip' Shape Pos xs0 ys.
