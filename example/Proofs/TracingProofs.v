From Base Require Import Free Free.Handlers Prelude Test.QuickCheck.
From Generated Require Import Proofs.Tracing.

Theorem trace_is_shared : quickCheckHandle (@prop_trace_is_shared _ _ cbneed _) HandlerShareTrace.
Proof.
  simpl. reflexivity.
Qed.
