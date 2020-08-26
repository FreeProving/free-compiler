From Base Require Import Free.
From Base Require Import Free.Instance.Identity.

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
