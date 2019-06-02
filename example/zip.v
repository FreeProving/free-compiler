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
  {F : Type -> Type} (C__F : Container F)
  {a b : Type} (xs : List C__F a) (ys : Free C__F (List C__F b))
  : Free C__F (List C__F (Pair C__F a b)) :=
  match xs with
  | Nil        => pure Nil
  | Cons x xs' =>
      ys >>= fun(ys0 : List C__F b) =>
        match ys0 with
        | Nil        => pure Nil
        | Cons y ys' => 
            pure (Cons (pure (Pair_ x y)) (
              xs' >>= fun(xs'0 : List C__F a) => zip' C__F xs'0 ys'
            ))
        end
  end.

Definition zip
  {F : Type -> Type} (C__F : Container F)
  {a b : Type} (xs : Free C__F (List C__F a)) (ys : Free C__F (List C__F b))
  : Free C__F (List C__F (Pair C__F a b)) :=
  xs >>= fun(xs0 : List C__F a) =>
    zip' C__F xs0 ys.