(* This file includes some examples that show the normalisation of
   some data types in a nondeterministic context. *)

From Base Require Import Free.
From Base Require Import Free.Handlers.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Instance.ND.
From Base Require Import Free.Util.Search.
From Base Require Import Prelude.

From Generated Require Import Proofs.TypeclassInstances.

Require Import Lists.List.
Import List.ListNotations.

(* Shortcuts for the Identity effect (i.e. the lack of an effect). *)
Notation IdS := Identity.Shape.
Notation IdP := Identity.Pos.

Section Data.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.

  Notation "'ND'" := (Injectable ND.Shape ND.Pos Shape Pos).

  Notation Bool_ := (Bool Shape Pos).
  Notation True' := (True_ Shape Pos).
  Notation False' := (False_ Shape Pos).

  Notation "x ? y" := (Choice Shape Pos x y) (at level 50).

  (* true : ([] ? [true ? false]) *)
  Definition ndList `{ND} : Free Shape Pos (MyList Shape Pos Bool_)
   := MyCons Shape Pos
        True'
        ( MyNil Shape Pos
        ? MyCons Shape Pos
          (True' ? False')
             (MyNil Shape Pos)).

  (* [true ? false] *)
  Definition ndList2 `{ND} : Free Shape Pos (MyList Shape Pos Bool_)
   := MyCons Shape Pos
        (True' ? False')
        (MyNil Shape Pos).

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
        (True' ? False')
        (Cons Shape Pos
          (Leaf Shape Pos)
          (Nil Shape Pos
          ? Cons Shape Pos
              (Leaf Shape Pos)
              (Nil Shape Pos))).

  (* branch true [branch true ? false []] *)
  Definition ndTree2 `{ND} : Free Shape Pos (Tree Shape Pos Bool_)
   := Branch Shape Pos
        True'
        (Cons Shape Pos
          (Branch Shape Pos (True' ? False') (Nil Shape Pos))
          (Nil Shape Pos)).

  (* (true -> (true ? false)) : ([] ? [(true ? false) -> false]) *)
  Definition ndMap `{ND} : Free Shape Pos (Map Shape Pos Bool_ Bool_)
   := Entry0 Shape Pos
        True'
        (True' ? False')
        ( Empty Shape Pos
        ? Entry0 Shape Pos
            (True' ? False')
            False'
            (Empty Shape Pos)).

End Data.

Arguments ndList {_} {_} {_}.
Arguments ndList2 {_} {_} {_}.
Arguments ndFoo {_} {_} {_}.
Arguments ndTree {_} {_} {_}.
Arguments ndTree2 {_} {_} {_}.
Arguments ndMap {_} {_} {_}.

(* Tests for the generated Normalform instances. *)

(* true : ([] ? [true ? false])
   --> [ [true], [true, true], [true, false] ] *)
Example nondeterministic_list : (@handle _ _ _ (HandlerND _)) _ ndList
  = [ myCons (pure true) (MyNil IdS IdP)
    ; myCons (pure true) (MyCons IdS IdP (pure true) (MyNil IdS IdP))
    ; myCons (pure true) (MyCons IdS IdP (pure false) (MyNil IdS IdP))
    ].
Proof. trivial. Qed.

(* (foo baz) ? (foo (bar (foo baz)))
   --> [ foo baz, foo (bar (foo baz)) ] *)
Example nondeterministic_foo : (@handle _ _ _ (HandlerND _)) _ ndFoo
  = [ foo (Bar0 IdS IdP (Foo0 IdS IdP (Baz IdS IdP)))
    ; foo (Baz IdS IdP)
    ].
Proof. trivial. Qed.

(* branch (true ? false) (leaf : ([] ? [leaf]))
   --> [ branch true leaf, branch true [leaf, leaf]
       , branch false leaf, branch false [leaf, leaf] ] *)
Example nondeterministic_tree : (@handle _ _ _ (HandlerND _)) _ ndTree
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
Example nondeterministic_map : (@handle _ _ _ (HandlerND _)) _ ndMap
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

(* Tests for the generated ShareableArgs instances. *)

(* let x = [true ? false] in myHead x || myHead x
   --> true || true ? false || false
   --> true ? false *)
Example deepSharingNDList
: (@handle _ _ _ (HandlerShareND _)) _ (doubleDisjunctionHead _ _ cbneed (ND.Partial _ _) ndList2)
= [true;false].
Proof. trivial. Qed.

(* let x = branch (true ? false) (leaf : ([] ? [leaf]))
   in root x || root x
   --> true || true ? false || false
   --> true ? false *)
Example deepSharingNDTree
: (@handle _ _ _ (HandlerShareND _)) _ (doubleDisjunctionRoot _ _ cbneed (ND.Partial _ _) ndTree)
= [true;false].
Proof. trivial. Qed.

(* let x = branch true [branch true ? false []]
   in headRoot x || headRoot x
   --> true || true ? false || false
   --> true ? false *)
Example deepSharingNDTree2
: (@handle _ _ _ (HandlerShareND _)) _ (doubleDisjunctionHeadRoot _ _ cbneed (ND.Partial _ _) ndTree2)
= [true;false].
Proof. trivial. Qed.

(* let x = true -> (true ? false)) : ([] ? [(true ? false) -> false]
   in firstMapEntry x || firstMapEntry x
   --> true || true ? false || false
   --> true ? false *)
Example deepSharingNDMap
: (@handle _ _ _ (HandlerShareND _)) _ (doubleDisjunctionMap _ _ cbneed (ND.Partial _ _) ndMap)
= [true;false].
Proof. trivial. Qed.
