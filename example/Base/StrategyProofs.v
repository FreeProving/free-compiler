From Base Require Import Free Free.Handlers Free.Instance.Maybe Prelude Test.QuickCheck.
From Generated Require Import Base.Strategy.

(* Proofs for Tracing Test Functions *)

Example add_traced_cbv : quickCheckHandle (@prop_add_traced_cbv _ _ Cbv _) HandlerTrace.
Proof. constructor. Qed.

Example add_traced_cbn : quickCheckHandle (@prop_add_traced_cbn _ _ Cbn _) HandlerTrace.
Proof. constructor. Qed.

Example add_traced_cbneed : quickCheckHandle (@prop_add_traced_cbneed _ _ Cbneed _) HandlerShareTrace.
Proof. constructor. Qed.


Example or_true_traced_cbv : quickCheckHandle (@prop_or_true_traced_cbv _ _ Cbv _) HandlerTrace.
Proof. constructor. Qed.

Example or_true_traced_cbn : quickCheckHandle (@prop_or_true_traced_cbn _ _ Cbn _) HandlerTrace.
Proof. constructor. Qed.

Example or_true_traced_cbneed : quickCheckHandle (@prop_or_true_traced_cbneed _ _ Cbneed _) HandlerShareTrace.
Proof. constructor. Qed.


Example or_false_traced_cbv : quickCheckHandle (@prop_or_false_traced_cbv _ _ Cbv _) HandlerTrace.
Proof. constructor. Qed.

Example or_false_traced_cbn : quickCheckHandle (@prop_or_false_traced_cbn _ _ Cbn _) HandlerTrace.
Proof. constructor. Qed.

Example or_false_traced_cbneed : quickCheckHandle (@prop_or_false_traced_cbneed _ _ Cbneed _) HandlerShareTrace.
Proof. constructor. Qed.


Example true_or_false_traced_cbv : quickCheckHandle (@prop_true_or_false_traced_cbv _ _ Cbv _) HandlerTrace.
Proof. constructor. Qed.

Example true_or_false_traced_cbn : quickCheckHandle (@prop_true_or_false_traced_cbn _ _ Cbn _) HandlerTrace.
Proof. constructor. Qed.

Example true_or_false_traced_cbneed : quickCheckHandle (@prop_true_or_false_traced_cbneed _ _ Cbneed _) HandlerShareTrace.
Proof. constructor. Qed.


Example false_or_true_traced_cbv : quickCheckHandle (@prop_false_or_true_traced_cbv _ _ Cbv _) HandlerTrace.
Proof. constructor. Qed.

Example false_or_true_traced_cbn : quickCheckHandle (@prop_false_or_true_traced_cbn _ _ Cbn _) HandlerTrace.
Proof. constructor. Qed.

Example false_or_true_traced_cbneed : quickCheckHandle (@prop_false_or_true_traced_cbneed _ _ Cbneed _) HandlerShareTrace.
Proof. constructor. Qed.


Example partial_traced_cbv : quickCheckHandle (@prop_partial_traced_cbv _ _ Cbv _ _) HandlerMaybeTrace.
Proof. constructor. Qed.

Example partial_traced_cbn : quickCheckHandle (@prop_partial_traced_cbn _ _ Cbn _ _) HandlerMaybeTrace.
Proof. constructor. Qed.

Example partial_traced_cbneed : quickCheckHandle (@prop_partial_traced_cbneed _ _ Cbneed _ _) HandlerMaybeShareTrace.
Proof. constructor. Qed.


(* Proofs for Non-Determinism Test Functions *)

Example add_non_det_cbv : quickCheckHandle (@prop_add_non_det_cbv _ _ Cbv _) HandlerND.
Proof. constructor. Qed.

Example add_non_det_cbn : quickCheckHandle (@prop_add_non_det_cbn _ _ Cbn _) HandlerND.
Proof. constructor. Qed.

Example add_non_det_cbneed : quickCheckHandle (@prop_add_non_det_cbneed _ _ Cbneed _) HandlerShareND.
Proof. constructor. Qed.


Example or_true_false_non_det_cbv : quickCheckHandle (@prop_or_true_false_non_det_cbv _ _ Cbv _) HandlerND.
Proof. constructor. Qed.

Example or_true_false_non_det_cbn : quickCheckHandle (@prop_or_true_false_non_det_cbn _ _ Cbn _) HandlerND.
Proof. constructor. Qed.

Example or_true_false_non_det_cbneed : quickCheckHandle (@prop_or_true_false_non_det_cbneed _ _ Cbneed _) HandlerShareND.
Proof. constructor. Qed.


Example partial_non_det_cbv : quickCheckHandle (@prop_partial_non_det_cbv _ _ Cbv (Maybe.Partial _ _) _) HandlerNDMaybe.
Proof. constructor. Qed.

Example partial_non_det_cbn : quickCheckHandle (@prop_partial_non_det_cbn _ _ Cbn (Maybe.Partial _ _) _) HandlerNDMaybe.
Proof. constructor. Qed.

Example partial_non_det_cbneed : quickCheckHandle (@prop_partial_non_det_cbneed _ _ Cbneed (Maybe.Partial _ _) _) HandlerShareNDMaybe.
Proof. constructor. Qed.

(* Proofs for Deep Sharing Test Functions *)

Example double_cbv : quickCheckHandle (@prop_double_cbv _ _ Cbv _) HandlerTrace.
Proof. constructor. Qed.

Example double_cbn : quickCheckHandle (@prop_double_cbn _ _ Cbn _) HandlerTrace.
Proof. constructor. Qed.

Example double_cbneed : quickCheckHandle (@prop_double_cbneed _ _ Cbneed _) HandlerShareTrace.
Proof. constructor. Qed.


Example double_maybe_cbv : quickCheckHandle (@prop_double_maybe_cbv _ _ Cbv _) HandlerTrace.
Proof. constructor. Qed.

Example double_maybe_cbn : quickCheckHandle (@prop_double_maybe_cbn _ _ Cbn _) HandlerTrace.
Proof. constructor. Qed.

Example double_maybe_cbneed : quickCheckHandle (@prop_double_maybe_cbneed _ _ Cbneed _) HandlerShareTrace.
Proof. constructor. Qed.
