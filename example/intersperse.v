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
  {F : Type -> Type} (C__F : Container F)
  (xs : List C__F Int) : Free C__F (List C__F Int) :=
  match xs with
  | Nil       => pure Nil
  | Cons y ys =>
    pure (Cons y (
      pure (Cons (pure 1%Z) (
        ys >>= fun(ys' : List C__F Int) => intersperseOneMatch' C__F ys'
      ))
    ))
  end.

Definition intersperseOneMatch
  {F : Type -> Type} (C__F : Container F)
  (xs : Free C__F (List C__F Int)) : Free C__F (List C__F Int) :=
  xs >>= fun(xs' : List C__F Int) =>
    intersperseOneMatch' C__F xs'.

Definition intersperseOne
  {F : Type -> Type} (C__F : Container F)
  (xs : Free C__F (List C__F Int)) : Free C__F (List C__F Int) :=
  pure (Cons (pure 1%Z) (intersperseOneMatch C__F xs)).

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
  {F : Type -> Type} (C__F : Container F)
  (xs : List C__F Int) : Free C__F (List C__F Int) :=
  match xs with
  | Nil       => pure Nil
  | Cons y ys =>
    pure (Cons y (
      pure (Cons (pure 1%Z) (
        ys >>= fun(ys' : List C__F Int) => intersperseOne' C__F ys'
      ))
    ))
  end.

Definition intersperseOne
  {F : Type -> Type} (C__F : Container F)
  (xs : Free C__F (List C__F Int)) : Free C__F (List C__F Int) :=
  pure (Cons (pure 1%Z) (
    xs >>= fun(xs' : List C__F Int) => intersperseOne' C__F xs')
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
  {F : Type -> Type} (C__F : Container F)
  {a : Type} (sep : Free C__F a) (xs : List C__F a) : Free C__F (List C__F a) :=
  match xs with
  | Nil       => pure Nil
  | Cons y ys =>
      pure (Cons y (
        ys >>= fun(ys0 : List C__F a) =>
          match ys0 with
          | Nil       => pure Nil
          | Cons z zs =>
              pure (Cons sep (
                ys >>= fun(ys1 : List C__F a) => intersperse'' C__F sep ys1
              ))
          end
      ))
  end.

Definition intersperse'
  {F : Type -> Type} (C__F : Container F)
  {a : Type} (sep : Free C__F a) (xs : Free C__F (List C__F a)) 
  : Free C__F (List C__F a) :=
  xs >>= fun(xs' : List C__F a) => intersperse'' C__F sep xs'.

End InterspersePrime.
