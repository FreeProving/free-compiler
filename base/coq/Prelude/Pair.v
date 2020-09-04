From Base Require Import Free.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Malias.

Section SecPair.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).

  Inductive Pair (A B : Type) : Type :=
    | pair_ : Free' A -> Free' B -> Pair A B.

  Arguments pair_ {A} {B}.

  (* smart constructor *)
  Definition Pair_ {A B : Type} (x : Free' A) (y : Free' B)
    : Free' (Pair A B) :=
    pure (pair_ x y).

  (* First element *)
  Definition fstPair {A B : Type} (fp : Free' (Pair A B))
   : Free Shape Pos A
  := fp >>= fun p => match p with
                    | pair_ x _ => x
                    end.

  (* Second element *)
  Definition sndPair {A B : Type} (fp : Free' (Pair A B))
   : Free Shape Pos B
  := fp >>= fun p => match p with
                    | pair_ _ y => y
                    end.

End SecPair.

Arguments pair_  {Shape} {Pos} {A} {B}.

(* Normalform instance for Pair *)
Section SecNFPair.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.

  Variable A B C D : Type.

  Definition nf'Pair `{Normalform Shape Pos A C}
                     `{Normalform Shape Pos B D}
                     (p : Pair Shape Pos A B)
    : Free Shape Pos (Pair Identity.Shape Identity.Pos C D)
   := match p with
       | pair_ fa fb => nf fa >>= fun na =>
                        nf fb >>= fun nb =>
                        pure (pair_ (pure na) (pure nb))
       end.

  Global Instance NormalformPair `{Normalform Shape Pos A C}
                                 `{Normalform Shape Pos B D}
    : Normalform Shape Pos (Pair Shape Pos A B)
                           (Pair Identity.Shape Identity.Pos C D)
   := { nf' := nf'Pair }.

End SecNFPair.

(* ShareableArgs instance for Pair *)
Instance ShareableArgsPair {Shape : Type} {Pos : Shape -> Type} (A B : Type)
                        `{Injectable Share.Shape Share.Pos Shape Pos}
                        `{SAA : ShareableArgs Shape Pos A}
                        `{SAB : ShareableArgs Shape Pos B}
  : ShareableArgs Shape Pos (Pair Shape Pos A B) := {
     shareArgs p := match p with
                    | pair_ fx fy => cbneed Shape Pos (@shareArgs Shape Pos A SAA) fx >>= fun sx =>
                                     cbneed Shape Pos (@shareArgs Shape Pos B SAB) fy >>= fun sy =>
                                     (pure (pair_ sx sy))
                    end
   }.
