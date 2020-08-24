From Base Require Import Free.
From Base Require Import Free.Instance.Identity.

(* We define an alias for [unit] that accepts the parameters [Shape] and
   [Pos] to unify the translation of build-in and user defined data types.
   We cannot define [Unit] in the section below, because Coq won't add
   [Variable]s to definitions that don't use them. *)
Definition Unit (Shape : Type) (Pos : Shape -> Type) : Type := unit.

Section SecUnit.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Notation "'Free''" := (Free Shape Pos).
  Notation "'Unit''" := (Unit Shape Pos).

  (* smart constructor *)
  Definition Tt : Free' Unit' := pure tt.

End SecUnit.

(* Normalform instance for Unit *)
Section SecNFUnit.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.

  Definition nfUnit (n : Free Shape Pos (Unit Shape Pos)) 
    := n >>= (fun n' => pure n').

  Lemma nf_impure_unit : forall s (pf : _ -> Free Shape Pos (Unit Shape Pos)),
      nfUnit (impure s pf) = impure s (fun p => nfUnit (pf p)).
  Proof. trivial. Qed.

  Lemma nf_pure_unit : forall (x : Unit Shape Pos),
      nfUnit (pure x) = pure x.
  Proof. trivial. Qed.

Global Instance NormalformUnit : Normalform (Unit Shape Pos) 
                                     (Unit Identity.Shape Identity.Pos)
 := {
      nf := nfUnit;
      nf_impure := nf_impure_unit;
      nf' := pure;
      nf_pure := nf_pure_unit
    }.

End SecNFUnit.