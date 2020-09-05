(** Instances for the Handler class. *)

From Base Require Import Free.
From Base Require Import Free.Instance.Error.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Instance.Maybe.
From Base Require Import Free.Instance.ND.
From Base Require Import Free.Instance.Share.
From Base Require Import Free.Instance.Trace.

From Base Require Import Free.Malias.

From Base Require Import Prelude.

From Base Require Import Free.Util.Search.

Require Import Coq.Lists.List.
Import List.ListNotations.

(* No effect *)

(* Identity handler *)
Instance HandlerNoEffect (A B : Type)
                         `{Normalform _ _ A B}:
 Handler Identity.Shape Identity.Pos A B := {
  handle p := run (nf p)
}.

(* One effect *)

(* Maybe :+: Identity handler *)

Definition SMId := Comb.Shape Maybe.Shape Identity.Shape.
Definition PMId := Comb.Pos Maybe.Pos Identity.Pos.

Instance HandlerMaybe (A B : Type)
  `{Normalform SMId PMId A B} :
 Handler SMId PMId A (option B) := {
  handle p := run (runMaybe (nf p))
}.

(* Error :+: Identity handler *)

Definition SErrId := Comb.Shape (Error.Shape string) Identity.Shape.
Definition PErrId := Comb.Pos (@Error.Pos string) Identity.Pos.

Instance HandlerError (A B : Type)
  `{Normalform SErrId PErrId A B} :
 Handler SErrId PErrId A (B + string) := {
  handle p := run (runError (nf p))
}.

Definition pUndefined {Shape : Type} {Pos : Shape -> Type} (P : Partial Shape Pos)
  := @undefined Shape Pos P (Bool Shape Pos).
Definition pError {Shape : Type} {Pos : Shape -> Type} (P : Partial Shape Pos) (msg : string)
  := @error Shape Pos P (Bool Shape Pos) msg.

Compute handle (pUndefined (Maybe.Partial _ _)).
Compute handle (pUndefined (Error.Partial _ _)).
Compute handle (pError (Maybe.Partial _ _) "Nope" ).
Compute handle (pError (Error.Partial _ _) "Nope" ).

(* ND :+: Identity handler *)
Definition SNDId := Comb.Shape ND.Shape Identity.Shape.
Definition PNDId := Comb.Pos ND.Pos Identity.Pos.

Instance HandlerND (A B : Type)
  `{Normalform SNDId PNDId A B}
  : Handler SNDId PNDId A (list B) := {
  handle p := collectVals (run (runChoice (nf p)))
}.

(* Trace :+: Identity handler *)

Definition STrcId := Comb.Shape Trace.Shape Identity.Shape.
Definition PTrcId := Comb.Pos Trace.Pos Identity.Pos.

Instance HandlerTrace (A B : Type)
                      `{Normalform STrcId PTrcId A B} :
 Handler STrcId PTrcId A (B * list string) := {
  handle p := collectMessages (run (runTracing (nf p)))
}.

(* Share :+: Identity handler *)

Definition SShrId := Comb.Shape Share.Shape Identity.Shape.
Definition PShrId := Comb.Pos Share.Pos Identity.Pos.

Instance HandlerShare (A B : Type)
                      `{Normalform SShrId PShrId A B} :
 Handler SShrId PShrId A B := {
  handle p := (run (runEmptySharing (0,0) (nf p)))
}.

(* Two effects *)

(* NOTE: There is no handler for an effect stack that contains both the Error and
   Maybe effects. Both effects model partiality, but only one interpretation of
   partiality is used at a time. *)

(* Share :+: ND :+: Identity handler *)

Definition SShrND := Comb.Shape Share.Shape (Comb.Shape ND.Shape Identity.Shape).
Definition PShrND := Comb.Pos Share.Pos (Comb.Pos ND.Pos Identity.Pos).

Instance HandlerSharingND (A B : Type)
                          `{Normalform SShrND PShrND A B}
 : Handler SShrND PShrND
         A (list B) := {
  handle p := collectVals (run (runChoice (runNDSharing (0,0) (nf p))))
}.

(* Share :+: Trace :+: Identity handler *)

Definition SShrTrc := Comb.Shape Share.Shape (Comb.Shape Trace.Shape Identity.Shape).
Definition PShrTrc := Comb.Pos Share.Pos (Comb.Pos Trace.Pos Identity.Pos).

Instance HandlerSharingTracing (A B : Type)
                               `{Normalform SShrTrc PShrTrc A B} :
 Handler SShrTrc PShrTrc A (B * list string) := {
  handle p := collectMessages (run (runTracing (runTraceSharing (0,0) (nf p))))
}.

(* Maybe :+: Share :+: Identity handler *)

Definition SMaybeShr := Comb.Shape Maybe.Shape (Comb.Shape Share.Shape Identity.Shape).
Definition PMaybeShr := Comb.Pos Maybe.Pos (Comb.Pos Share.Pos Identity.Pos).

Instance HandlerMaybeShare (A B : Type)
                               `{Normalform SMaybeShr PMaybeShr A B} :
 Handler SMaybeShr PMaybeShr A (option B) := {
  handle p := run (runEmptySharing (0,0) (runMaybe (nf p)))
}.

(* Maybe :+: ND :+: Identity handler *)
(* If an undefined value is evaluated in one non-deterministic branch of a program,
   it should not affect the other branches.
   Therefore, the maybe effect is handled before the non-determinism effect. *)

Definition SMaybeND := Comb.Shape Maybe.Shape (Comb.Shape ND.Shape Identity.Shape).
Definition PMaybeND := Comb.Pos Maybe.Pos (Comb.Pos ND.Pos Identity.Pos).

Instance HandlerMaybeND (A B : Type)
                               `{Normalform SMaybeND PMaybeND A B} :
 Handler SMaybeND PMaybeND A (list (option B)) := {
  handle p := collectVals (run (runChoice (runMaybe (nf p))))
}.

(* Maybe :+: Trace :+: Identity handler *)
(* In Haskell, when an undefined value is evaluated in a traced program, 
   the message log until that point is still displayed.
   Therefore, the maybe effect is handled before the tracing effect. *)

Definition SMaybeTrc := Comb.Shape Maybe.Shape (Comb.Shape Trace.Shape Identity.Shape).
Definition PMaybeTrc := Comb.Pos Maybe.Pos (Comb.Pos Trace.Pos Identity.Pos).

Instance HandlerMaybeTrc (A B : Type)
                               `{Normalform SMaybeTrc PMaybeTrc A B} :
 Handler SMaybeTrc PMaybeTrc A (option B * list string) := {
  handle p := collectMessages (run (runTracing (runMaybe (nf p))))
}.

(* Error :+: Share :+: Identity handler *)

Definition SErrShr := Comb.Shape (Error.Shape string) (Comb.Shape Share.Shape Identity.Shape).
Definition PErrShr := Comb.Pos (@Error.Pos string) (Comb.Pos Share.Pos Identity.Pos).

Instance HandlerErrorShare (A B : Type)
                               `{Normalform SErrShr PErrShr A B} :
 Handler SErrShr PErrShr A (B + string) := {
  handle p := run (runEmptySharing (0,0) (runError (nf p)))
}.

(* Error :+: ND :+: Identity handler *)
(* If an error is thrown in one non-deterministic branch of a program,
   it should not affect the other branches.
   Therefore, the error effect is handled before the non-determinism effect. *)

Definition SErrND := Comb.Shape (Error.Shape string) (Comb.Shape ND.Shape Identity.Shape).
Definition PErrND := Comb.Pos (@Error.Pos string) (Comb.Pos ND.Pos Identity.Pos).

Instance HandlerErrorND (A B : Type)
                               `{Normalform SErrND PErrND A B} :
 Handler SErrND PErrND A (list (B + string)) := {
  handle p := collectVals (run (runChoice (runError (nf p))))
}.

(* Error :+: Trace :+: Identity handler *)
(* In Haskell, when an error is thrown in a traced program, the message log until that point
   is displayed alongside the error message.
   Therefore, the error effect is handled before the tracing effect. *)

Definition SErrorTrc := Comb.Shape (Error.Shape string) (Comb.Shape Trace.Shape Identity.Shape).
Definition PErrorTrc := Comb.Pos (@Error.Pos string) (Comb.Pos Trace.Pos Identity.Pos).

Instance HandlerErrorTrc (A B : Type)
                               `{Normalform SErrorTrc PErrorTrc A B} :
 Handler SErrorTrc PErrorTrc A ((B + string) * list string) := {
  handle p := collectMessages (run (runTracing (runError (nf p))))
}.

Compute handle (trace "Hey!" (trace "Ho!" (error "Nope"))).

(* Trace :+: ND :+: Identity handler *)

Definition STrcND := Comb.Shape Trace.Shape (Comb.Shape ND.Shape Identity.Shape).
Definition PTrcND := Comb.Pos Trace.Pos (Comb.Pos ND.Pos Identity.Pos).

Instance HandlerTraceND (A B : Type)
                               `{Normalform STrcND PTrcND A B} :
 Handler STrcND PTrcND A (list (B * list string)) := {
  handle p := map (@collectMessages B)
                  (@collectVals (B * list (option Sharing.ID * string))
                                (run (runChoice (runTracing (nf p)))))
}.


(* Three effects *)

(* NOTE: There is no handler for an effect stack that contains sharing,
   non-determinism and tracing. This is because only one effect can be
   shared in a program. *)

(* Maybe :+: Share :+: ND :+: Identity handler *)

Definition SMaybeShrND :=
  Comb.Shape Maybe.Shape
    (Comb.Shape Share.Shape
      (Comb.Shape ND.Shape Identity.Shape)).

Definition PMaybeShrND :=
  Comb.Pos Maybe.Pos
    (Comb.Pos Share.Pos
      (Comb.Pos ND.Pos Identity.Pos)).

Instance HandlerSharingNDMaybe (A B : Type)
                               `{Normalform SMaybeShrND PMaybeShrND A B} :
 Handler SMaybeShrND PMaybeShrND A (list (option B)) := {
  handle p := collectVals (run (runChoice (runNDSharing (0,0) (runMaybe (nf p)))))
}.

(* Maybe :+: Share :+: Trace :+: Identity handler *)

Definition SMaybeShrTrc :=
  Comb.Shape Maybe.Shape
    (Comb.Shape Share.Shape
      (Comb.Shape Trace.Shape Identity.Shape)).

Definition PMaybeShrTrc :=
  Comb.Pos Maybe.Pos
    (Comb.Pos Share.Pos
      (Comb.Pos Trace.Pos Identity.Pos)).

Instance HandlerMaybeShareTrace (A B : Type)
                               `{Normalform SMaybeShrTrc PMaybeShrTrc A B} :
 Handler SMaybeShrTrc PMaybeShrTrc A (option B * list string) := {
  handle p := collectMessages (run (runTracing (runTraceSharing (0,0) (runMaybe (nf p)))))
}.

(* Maybe :+: Trace :+: ND :+: Identity handler *)

Definition SMaybeTrcND :=
  Comb.Shape Maybe.Shape
    (Comb.Shape Trace.Shape
      (Comb.Shape ND.Shape Identity.Shape)).

Definition PMaybeTrcND :=
  Comb.Pos Maybe.Pos
    (Comb.Pos Trace.Pos
      (Comb.Pos ND.Pos Identity.Pos)).

Instance HandlerMaybeTrcND (A B : Type)
                               `{Normalform SMaybeTrcND PMaybeTrcND A B} :
 Handler SMaybeTrcND PMaybeTrcND A (list (option B * list string)) := {
  handle p := map (@collectMessages (option B))
                  (@collectVals (option B * list (option Sharing.ID * string))
                                (run (runChoice (runTracing (runMaybe (nf p))))))
}.

(* Error :+: Share :+: ND :+: Identity handler *)

Definition SErrShrND :=
  Comb.Shape (Error.Shape string)
    (Comb.Shape Share.Shape
      (Comb.Shape ND.Shape Identity.Shape)).

Definition PErrShrND :=
  Comb.Pos (@Error.Pos string)
    (Comb.Pos Share.Pos
      (Comb.Pos ND.Pos Identity.Pos)).

Instance HandlerErrorSharingND (A B : Type)
                               `{Normalform SErrShrND PErrShrND A B} :
 Handler SErrShrND PErrShrND A (list (B + string)) := {
  handle p := collectVals (run (runChoice (runNDSharing (0,0) (runError (nf p)))))
}.

(* Error :+: Share :+: Trace :+: Identity handler *)

Definition SErrShrTrc :=
  Comb.Shape (Error.Shape string)
    (Comb.Shape Share.Shape
      (Comb.Shape Trace.Shape Identity.Shape)).

Definition PErrShrTrc :=
  Comb.Pos (@Error.Pos string)
    (Comb.Pos Share.Pos
      (Comb.Pos Trace.Pos Identity.Pos)).

Instance HandlerErrorShareTrace (A B : Type)
                               `{Normalform SErrShrTrc PErrShrTrc A B} :
 Handler SErrShrTrc PErrShrTrc A ((B + string) * list string) := {
  handle p := collectMessages (run (runTracing (runTraceSharing (0,0) (runError (nf p)))))
}.

(* Error :+: Trace :+: ND :+: Identity handler *)

Definition SErrTrcND :=
  Comb.Shape (Error.Shape string)
    (Comb.Shape Trace.Shape
      (Comb.Shape ND.Shape Identity.Shape)).

Definition PErrTrcND :=
  Comb.Pos (@Error.Pos string)
    (Comb.Pos Trace.Pos
      (Comb.Pos ND.Pos Identity.Pos)).

Instance HandlerErrorTrcND (A B : Type)
                               `{Normalform SErrTrcND PErrTrcND A B} :
 Handler SErrTrcND PErrTrcND A (list ((B + string) * list string)) := {
  handle p := map (@collectMessages (B + string))
                  (@collectVals ((B + string) * list (option Sharing.ID * string))
                                (run (runChoice (runTracing (runError (nf p))))))
}.
