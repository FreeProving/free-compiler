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

Definition nfPair `{Normalform Shape Pos A C}
                  `{Normalform Shape Pos B D}
                  (p : Free Shape Pos (Pair Shape Pos A B))
  : Free Shape Pos (Pair Identity.Shape Identity.Pos C D)
 := p >>= (fun p' => nf'Pair p').

Lemma nf_impure_pair `{Normalform Shape Pos A C}
                     `{Normalform Shape Pos B D}
  : forall s (pf : _ -> Free Shape Pos (Pair Shape Pos A B)),
    nfPair (impure s pf) = impure s (fun p => nfPair (pf p)).
Proof. trivial. Qed.

Lemma nf_pure_pair `{Normalform Shape Pos A C}
                   `{Normalform Shape Pos B D}
  : forall (x : Pair Shape Pos A B),
    nfPair (pure x) = nf'Pair x.
Proof. trivial. Qed.

Global Instance NormalformPair `{Normalform Shape Pos A C}
                        `{Normalform Shape Pos B D}
  : Normalform (Pair Shape Pos A B) 
               (Pair Identity.Shape Identity.Pos C D)
 := {
      nf := nfPair;
      nf_impure := nf_impure_pair;
      nf' := nf'Pair;
      nf_pure := nf_pure_pair
    }.

End SecNFPair.

(* ShareableArgs instance for Pair *)

Instance ShareableArgsPair {Shape : Type} {Pos : Shape -> Type} (A B : Type)
                        `{Injectable Share.Shape Share.Pos Shape Pos}
                        `{ShareableArgs Shape Pos A}
                        `{ShareableArgs Shape Pos B}
  : ShareableArgs Shape Pos (Pair Shape Pos A B) := {
     shareArgs p := match p with
                    | pair_ fx fy => cbneed Shape Pos fx >>= fun sx =>
                                     cbneed Shape Pos fy >>= fun sy =>
                                     (pure (pair_ sx sy)) 
                    end
   }.
