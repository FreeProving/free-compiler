From Base Require Import Free Free.Handlers Free.Instance.Maybe Free.Instance.Share Prelude Test.QuickCheck.
From Generated Require Import Base.Strategy.

Require Import Coq.Logic.FunctionalExtensionality.

(* Proofs for Trivial Test Functions *)

Example example_true: quickCheck prop_true.
Proof. constructor. Qed.

Example example_id_true_cbv: quickCheck (withStrategy Cbv prop_id_true).
Proof. constructor. Qed.

Example example_id_true_cbn: quickCheck (withStrategy Cbn prop_id_true).
Proof. constructor. Qed.

Example example_id_true_cbneed: ~ quickCheck (withSharing prop_id_true).
Proof.
  unfold quickCheck. simpl. intros H.
  specialize (H Share.Shape Share.Pos Inject_refl). apply H.
Qed.

(* Proofs for Tracing Test Functions *)

Example add_traced_cbv : quickCheckHandle (@prop_add_traced_cbv _ _ cbv _) HandlerTrace.
Proof. constructor. Qed.

Example add_traced_cbn : quickCheckHandle (@prop_add_traced_cbn _ _ cbn _) HandlerTrace.
Proof. constructor. Qed.

Example add_traced_cbneed : quickCheckHandle (@prop_add_traced_cbneed _ _ cbneed _) HandlerShareTrace.
Proof. constructor. Qed.


Example or_true_traced_cbv : quickCheckHandle (@prop_or_true_traced_cbv _ _ cbv _) HandlerTrace.
Proof. constructor. Qed.

Example or_true_traced_cbn : quickCheckHandle (@prop_or_true_traced_cbn _ _ cbn _) HandlerTrace.
Proof. constructor. Qed.

Example or_true_traced_cbneed : quickCheckHandle (@prop_or_true_traced_cbneed _ _ cbneed _) HandlerShareTrace.
Proof. constructor. Qed.


Example or_false_traced_cbv : quickCheckHandle (@prop_or_false_traced_cbv _ _ cbv _) HandlerTrace.
Proof. constructor. Qed.

Example or_false_traced_cbn : quickCheckHandle (@prop_or_false_traced_cbn _ _ cbn _) HandlerTrace.
Proof. constructor. Qed.

Example or_false_traced_cbneed : quickCheckHandle (@prop_or_false_traced_cbneed _ _ cbneed _) HandlerShareTrace.
Proof. constructor. Qed.


Example true_or_false_traced_cbv : quickCheckHandle (@prop_true_or_false_traced_cbv _ _ cbv _) HandlerTrace.
Proof. constructor. Qed.

Example true_or_false_traced_cbn : quickCheckHandle (@prop_true_or_false_traced_cbn _ _ cbn _) HandlerTrace.
Proof. constructor. Qed.

Example true_or_false_traced_cbneed : quickCheckHandle (@prop_true_or_false_traced_cbneed _ _ cbneed _) HandlerShareTrace.
Proof. constructor. Qed.


Example false_or_true_traced_cbv : quickCheckHandle (@prop_false_or_true_traced_cbv _ _ cbv _) HandlerTrace.
Proof. constructor. Qed.

Example false_or_true_traced_cbn : quickCheckHandle (@prop_false_or_true_traced_cbn _ _ cbn _) HandlerTrace.
Proof. constructor. Qed.

Example false_or_true_traced_cbneed : quickCheckHandle (@prop_false_or_true_traced_cbneed _ _ cbneed _) HandlerShareTrace.
Proof. constructor. Qed.


Example partial_traced_cbv : quickCheckHandle (@prop_partial_traced_cbv _ _ cbv _ _) HandlerMaybeTrace.
Proof. constructor. Qed.

Example partial_traced_cbn : quickCheckHandle (@prop_partial_traced_cbn _ _ cbn _ _) HandlerMaybeTrace.
Proof. constructor. Qed.

Example partial_traced_cbneed : quickCheckHandle (@prop_partial_traced_cbneed _ _ cbneed _ _) HandlerMaybeShareTrace.
Proof. constructor. Qed.


(* Proofs for Non-Determinism Test Functions *)

Example add_non_det_cbv : quickCheckHandle (@prop_add_non_det_cbv _ _ cbv _) HandlerND.
Proof. constructor. Qed.

Example add_non_det_cbn : quickCheckHandle (@prop_add_non_det_cbn _ _ cbn _) HandlerND.
Proof. constructor. Qed.

Example add_non_det_cbneed : quickCheckHandle (@prop_add_non_det_cbneed _ _ cbneed _) HandlerShareND.
Proof. constructor. Qed.


Example or_true_false_non_det_cbv : quickCheckHandle (@prop_or_true_false_non_det_cbv _ _ cbv _) HandlerND.
Proof. constructor. Qed.

Example or_true_false_non_det_cbn : quickCheckHandle (@prop_or_true_false_non_det_cbn _ _ cbn _) HandlerND.
Proof. constructor. Qed.

Example or_true_false_non_det_cbneed : quickCheckHandle (@prop_or_true_false_non_det_cbneed _ _ cbneed _) HandlerShareND.
Proof. constructor. Qed.


Example partial_non_det_cbv : quickCheckHandle (@prop_partial_non_det_cbv _ _ cbv (Maybe.Partial _ _) _) HandlerNDMaybe.
Proof. constructor. Qed.

Example partial_non_det_cbn : quickCheckHandle (@prop_partial_non_det_cbn _ _ cbn (Maybe.Partial _ _) _) HandlerNDMaybe.
Proof. constructor. Qed.

Example partial_non_det_cbneed : quickCheckHandle (@prop_partial_non_det_cbneed _ _ cbneed (Maybe.Partial _ _) _) HandlerShareNDMaybe.
Proof. constructor. Qed.

(* Proofs for Deep Sharing Test Functions *)

Example double_cbv : quickCheckHandle (@prop_double_cbv _ _ cbv _) HandlerTrace.
Proof. constructor. Qed.

Example double_cbn : quickCheckHandle (@prop_double_cbn _ _ cbn _) HandlerTrace.
Proof. constructor. Qed.

Example double_cbneed : quickCheckHandle (@prop_double_cbneed _ _ cbneed _) HandlerShareTrace.
Proof. constructor. Qed.


Example double_maybe_cbv : quickCheckHandle (@prop_double_maybe_cbv _ _ cbv _) HandlerTrace.
Proof. constructor. Qed.

Example double_maybe_cbn : quickCheckHandle (@prop_double_maybe_cbn _ _ cbn _) HandlerTrace.
Proof. constructor. Qed.

Example double_maybe_cbneed : quickCheckHandle (@prop_double_maybe_cbneed _ _ cbneed _) HandlerShareTrace.
Proof. constructor. Qed.
