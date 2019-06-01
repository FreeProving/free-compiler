(******************************************************************************
 * Predefined functions and datatypes                                         *
 *****************************************************************************)

Require Import ZArith.
Definition Int : Type := Z.

Definition m : Type -> Type := option.
Definition m_return {a : Type} (x : a) : m a := Some x.
Definition m_bind {a b : Type} (mx : m a) (f : a -> m b) : m b :=
  match mx with
  | None   => None
  | Some x => f x
  end.

Notation "mx >>= f" := (m_bind mx f) (left associativity, at level 50).

Inductive List (a : Type) : Type :=
  | Nil  : List a
  | Cons : m a -> m (List a) -> List a.

Arguments Nil {a}.
Arguments Cons {a}.

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

Fixpoint intersperseOneMatch' (xs : List Int) : m (List Int) :=
  match xs with
  | Nil       => m_return Nil
  | Cons y ys =>
    m_return (Cons y (
      m_return (Cons (m_return 1%Z) (
        ys >>= fun(ys' : List Int) => intersperseOneMatch' ys'
      ))
    ))
  end.

Definition intersperseOneMatch (xs : m (List Int)) : m (List Int) :=
  xs >>= fun(xs' : List Int) =>
    intersperseOneMatch' xs'.

Definition intersperseOne (xs : m (List Int)) : m (List Int) :=
  m_return (Cons (m_return 1%Z) (intersperseOneMatch xs)).

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

Fixpoint intersperseOne' (xs : List Int) : m (List Int) :=
  match xs with
  | Nil       => m_return Nil
  | Cons y ys =>
    m_return (Cons y (
      m_return (Cons (m_return 1%Z) (
        ys >>= fun(ys' : List Int) => intersperseOne' ys'
      ))
    ))
  end.

Definition intersperseOne (xs : m (List Int)) : m (List Int) :=
  m_return (Cons (m_return 1%Z) (xs >>= fun(xs' : List Int) => intersperseOne' xs')).

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

Fixpoint intersperse'' {a : Type} (sep : m a) (xs : List a) : m (List a) :=
  match xs with
  | Nil       => m_return Nil
  | Cons y ys =>
      m_return (Cons y (
        ys >>= fun(ys0 : List a) =>
          match ys0 with
          | Nil       => m_return Nil
          | Cons z zs =>
              m_return (Cons sep (
                ys >>= fun(ys1 : List a) => intersperse'' sep ys1
              ))
          end
      ))
  end.

Definition intersperse' {a : Type} (sep : m a) (xs : m (List a)) : m (List a) :=
  xs >>= fun(xs' : List a) => intersperse'' sep xs'.

End InterspersePrime.
