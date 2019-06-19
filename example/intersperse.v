From Base Require Import Prelude.
From Base Require Import Free.

(*****************************************************************************)

Module IntersperseOneOldApproach.

(*
  Translation of `intersperseOne` with current approach by splitting and
  inlining

  ```haskell
  intersperseOneMatch :: [Int] -> [Int]
  intersperseOneMatch xs =
    case xs of
      [] -> []
      y:ys  -> y : (1 : intersperseOneMatch ys)

  intersperseOne :: [Int] -> [Int]
  intersperseOne xs =
    1 : intersperseOneMatch xs
  ```
*)

Fixpoint intersperseOneMatch'
  (Shape : Type) (Pos : Shape -> Type)
  (xs : List Shape Pos Int) 
  : Free Shape Pos (List Shape Pos Int) :=
  match xs with
  | nil       => Nil
  | cons y ys =>
    Cons y (
      Cons (pure 1%Z) (
        ys >>= fun(ys' : List Shape Pos Int) => 
          intersperseOneMatch' Shape Pos ys'
      )
    )
  end.

Definition intersperseOneMatch
  (Shape : Type) (Pos : Shape -> Type)
  (xs : Free Shape Pos (List Shape Pos Int)) 
  : Free Shape Pos (List Shape Pos Int) :=
  xs >>= fun(xs' : List Shape Pos Int) =>
    intersperseOneMatch' Shape Pos xs'.

Definition intersperseOne
  (Shape : Type) (Pos : Shape -> Type)
  (xs : Free Shape Pos (List Shape Pos Int)) 
  : Free Shape Pos (List Shape Pos Int) :=
  Cons (pure 1%Z) (intersperseOneMatch Shape Pos xs).

End IntersperseOneOldApproach.

Module IntersperseOneNewApproach.

(*
  Translation of `intersperseOne` with new approach

  ```haskell
  intersperseOne :: [Int] -> [Int]
  intersperseOne xs =
    1 : case xs of
             [] -> []
             y:ys  -> y : intersperseOne ys
  ```
*)

Fixpoint intersperseOne'
  (Shape : Type) (Pos : Shape -> Type)
  (xs : List Shape Pos Int) : Free Shape Pos (List Shape Pos Int) :=
  match xs with
  | nil       => Nil
  | cons y ys =>
    Cons y (
      Cons (pure 1%Z) (
        ys >>= fun(ys' : List Shape Pos Int) => intersperseOne' Shape Pos ys'
      )
    )
  end.

Definition intersperseOne
  (Shape : Type) (Pos : Shape -> Type)
  (xs : Free Shape Pos (List Shape Pos Int)) 
  : Free Shape Pos (List Shape Pos Int) :=
  Cons (pure 1%Z) (
    xs >>= fun(xs' : List Shape Pos Int) => intersperseOne' Shape Pos xs'
  ).

End IntersperseOneNewApproach.

Module InterspersePrime.

(*
  Translation of `intersperse'` with current approach

  ```haskell
  intersperse' :: a -> [a] -> [a]
  intersperse' sep xs = case xs of
                         []   -> []
                         y:ys -> y : case ys of
                                       [] -> []
                                       _  -> sep : intersperse sep xs
  --                                   ^           ^^^^^^^^^^^     ^^
  --                                 z:zs         intersperse'     ys
  ```
*)

Fixpoint intersperse''
  (Shape : Type) (Pos : Shape -> Type)
  {a : Type} (sep : Free Shape Pos a) (xs : List Shape Pos a) 
  : Free Shape Pos (List Shape Pos a) :=
  match xs with
  | nil       => Nil
  | cons y ys =>
      Cons y (
        ys >>= fun(ys0 : List Shape Pos a) =>
          match ys0 with
          | nil       => Nil
          | cons z zs =>
              Cons sep (
                ys >>= fun(ys1 : List Shape Pos a) =>
                  intersperse'' Shape Pos sep ys1
              )
          end
      )
  end.

Definition intersperse'
  (Shape : Type) (Pos : Shape -> Type)
  {a : Type} (sep : Free Shape Pos a) (xs : Free Shape Pos (List Shape Pos a))
  : Free Shape Pos (List Shape Pos a) :=
  xs >>= fun(xs' : List Shape Pos a) => intersperse'' Shape Pos sep xs'.

End InterspersePrime.
