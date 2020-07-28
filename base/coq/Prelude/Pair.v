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

(* Normalform instance *)

Definition nf'Pair (Shape : Type) (Pos : Shape -> Type)
                   (A B C D : Type) 
                   `{Normalform Shape Pos A C}
                   `{Normalform Shape Pos B D}
                   (p : Pair Shape Pos A B)
  : Free Shape Pos (Pair Identity.Shape Identity.Pos C D)
 := match p with
     | pair_ fa fb => nf fa >>= fun na =>
                      nf fb >>= fun nb =>
                      pure (pair_ (pure na) (pure nb))
     end.

Definition nfPair (Shape : Type) (Pos : Shape -> Type)
                  (A B C D : Type)
                  `{Normalform Shape Pos A C}
                  `{Normalform Shape Pos B D}
                  (p : Free Shape Pos (Pair Shape Pos A B))
  : Free Shape Pos (Pair Identity.Shape Identity.Pos C D)
 := p >>= (fun p' => nf'Pair Shape Pos A B C D p').

Lemma nf_impure_pair (Shape : Type) (Pos : Shape -> Type)
                     (A B C D : Type)
                     `{Normalform Shape Pos A C}
                     `{Normalform Shape Pos B D}
  : forall s (pf : _ -> Free Shape Pos (Pair Shape Pos A B)),
    nfPair Shape Pos A B C D (impure s pf) = impure s (fun p => nfPair Shape Pos A B C D (pf p)).
Proof. trivial. Qed.

Lemma nf_pure_pair (Shape : Type) (Pos : Shape -> Type)
                   (A B C D : Type)
                   `{Normalform Shape Pos A C}
                   `{Normalform Shape Pos B D}
  : forall (x : Pair Shape Pos A B),
    nfPair Shape Pos A B C D (pure x) = nf'Pair Shape Pos A B C D x.
Proof. trivial. Qed.

Instance NormalformPair (Shape : Type) (Pos : Shape -> Type) (A B C D : Type)
                        `{Normalform Shape Pos A C}
                        `{Normalform Shape Pos B D}
  : Normalform Shape Pos (Pair Shape Pos A B) 
                         (Pair Identity.Shape Identity.Pos C D)
 := {
      nf := nfPair Shape Pos A B C D;
      nf_impure := nf_impure_pair Shape Pos A B C D;
      nf' := nf'Pair Shape Pos A B C D;
      nf_pure := nf_pure_pair Shape Pos A B C D
    }.
