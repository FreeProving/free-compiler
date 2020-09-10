(* This file includes some examples that show the normalisation of
   some data types in a nondeterministic context. *)

From Base Require Import Free.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Instance.ND.
From Base Require Import Free.Util.Search.
From Base Require Import Prelude.

From Generated Require Import Proofs.Normalform.

Require Import Lists.List.
Import List.ListNotations.

(* Shortcuts to handle a program. *)

(* Shortcut to evaluate a non-deterministic program to a result list.
   list without normalization. *)
Definition evalND {A : Type} (p : Free _ _ A)
:= @collectVals A (run (runChoice p)).

(* Handle a non-deterministic program after normalization. *)
Definition evalNDNF {A B : Type} 
                    `{Normalform _ _ A B}
  p := evalND (nf p).

(* Shortcuts for the Identity effect (i.e. the lack of an effect). *)
Notation IdS := Identity.Shape.
Notation IdP := Identity.Pos.

Section Data.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.

  Notation "'ND'" := (Injectable ND.Shape ND.Pos Shape Pos).

  Notation Bool_ := (Bool Shape Pos).
  Notation True_ := (True_ Shape Pos).
  Notation False_ := (False_ Shape Pos).

  Notation "x ? y" := (Choice Shape Pos x y) (at level 50).

  (* true : ([] ? [true ? false]) *)
  Definition ndList `{ND} : Free Shape Pos (MyList Shape Pos Bool_)
   := MyCons Shape Pos
        True_
        ( MyNil Shape Pos
        ? MyCons Shape Pos
          (True_ ? False_)
             (MyNil Shape Pos)).

  (* (foo (bar (foo baz))) ? (foo baz) *)
  Definition ndFoo `{ND} : Free Shape Pos (Foo Shape Pos Bool_)
   := Foo0 Shape Pos
        ( Bar0 Shape Pos
            (Foo0 Shape Pos
              (Baz Shape Pos))
        ? Baz Shape Pos).

  (* branch (true ? false) (leaf : ([] ? [leaf])) *)
  Definition ndTree `{ND} : Free Shape Pos (Tree Shape Pos Bool_)
   := Branch Shape Pos
        (True_ ? False_)
        (Cons Shape Pos
          (Leaf Shape Pos)
          ( Nil Shape Pos
          ? Cons Shape Pos
              (Leaf Shape Pos)
              (Nil Shape Pos))).

  (* (true -> (true ? false)) : ([] ? [(true ? false) -> false]) *)
  Definition ndMap `{ND} : Free Shape Pos (Map Shape Pos Bool_ Bool_)
   := Entry0 Shape Pos
        True_
        (True_ ? False_)
        ( Empty Shape Pos
        ? Entry0 Shape Pos
            (True_ ? False_)
            False_
            (Empty Shape Pos)).

End Data.

Arguments ndList {_} {_} {_}.
Arguments ndFoo {_} {_} {_}.
Arguments ndTree {_} {_} {_}.
Arguments ndMap {_} {_} {_}.

(* true : ([] ? [true ? false])
   --> [ [true], [true, true], [true, false] ] *)
Example nondeterministic_list : evalNDNF ndList
  = [ myCons (pure true) (MyNil IdS IdP)
    ; myCons (pure true) (MyCons IdS IdP (pure true) (MyNil IdS IdP))
    ; myCons (pure true) (MyCons IdS IdP (pure false) (MyNil IdS IdP))
    ].
Proof. trivial. Qed.

(* (foo baz) ? (foo (bar (foo baz)))
   --> [ foo baz, foo (bar (foo baz)) ] *)
Example nondeterministic_foo : evalNDNF ndFoo
  = [ foo (Bar0 IdS IdP (Foo0 IdS IdP (Baz IdS IdP)))
    ; foo (Baz IdS IdP)
    ].
Proof. trivial. Qed.

(* branch (true ? false) (leaf : ([] ? [leaf]))
   --> [ branch true leaf, branch true [leaf, leaf]
       , branch false leaf, branch false [leaf, leaf] ] *)
Example nondeterministic_tree : evalNDNF ndTree
  = [ branch (pure true) (Cons IdS IdP (Leaf IdS IdP) (Nil IdS IdP))
    ; branch (pure true) (Cons IdS IdP (Leaf IdS IdP)
        (Cons IdS IdP (Leaf IdS IdP) (Nil IdS IdP)))
    ; branch (pure false) (Cons IdS IdP (Leaf IdS IdP) (Nil IdS IdP))
    ; branch (pure false) (Cons IdS IdP (Leaf IdS IdP)
        (Cons IdS IdP (Leaf IdS IdP) (Nil IdS IdP)))
    ].
Proof. trivial. Qed.

(* (true -> (true ? false)) : ([] ? [(true ? false) -> false]) 
   --> [ [true -> true]                , [true -> true, true -> false]
       , [true -> true, false -> false], [false -> true]
       , [false -> true, true -> false], [false -> true, false -> false] ] *)
Example nondeterministic_map : evalNDNF ndMap
 = [ entry (pure true) (pure true) (Empty IdS IdP)
   ; entry (pure true) (pure true)
      (Entry0 IdS IdP (pure true) (pure false) (Empty IdS IdP))
   ; entry (pure true) (pure true)
      (Entry0 IdS IdP (pure false) (pure false) (Empty IdS IdP))
   ; entry (pure true) (pure false) (Empty IdS IdP)
   ; entry (pure true) (pure false)
      (Entry0 IdS IdP (pure true) (pure false) (Empty IdS IdP))
   ; entry (pure true) (pure false)
      (Entry0 IdS IdP (pure false) (pure false) (Empty IdS IdP))
   ].
Proof. trivial. Qed.
