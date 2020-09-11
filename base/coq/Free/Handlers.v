(** This module contains default handlers for individual effect stacks. *)

From Base Require Import Free.
From Base Require Import Free.Instance.Comb.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Instance.Maybe.
From Base Require Import Free.Instance.ND.
From Base Require Import Free.Instance.Share.
From Base Require Import Free.Instance.Trace.

From Base Require Import Prelude.

From Base Require Import Free.Util.Search.

Require Import Coq.Lists.List.
Import List.ListNotations.

(* No effect *)

(* Identity handler *)
Definition handleNoEffect {A B : Type}
                          `{Normalform _ _ A B}
                          (p : Free Identity.Shape Identity.Pos A) : B
:=  run (nf p).

(* One effect *)

(* Maybe :+: Identity handler *)

Definition SMId := Comb.Shape Maybe.Shape Identity.Shape.
Definition PMId := Comb.Pos Maybe.Pos Identity.Pos.

Definition handleMaybe {A B : Type}
  `{Normalform SMId PMId A B}
  (p : Free SMId PMId A) : option B := run (runMaybe (nf p)).

(* ND :+: Identity handler *)
Definition SNDId := Comb.Shape ND.Shape Identity.Shape.
Definition PNDId := Comb.Pos ND.Pos Identity.Pos.

Definition handleND {A B : Type}
  `{Normalform SNDId PNDId A B}
  (p : Free SNDId PNDId A) : list B
:= collectVals (run (runChoice (nf p))).

(* Trace :+: Identity handler *)

Definition STrcId := Comb.Shape Trace.Shape Identity.Shape.
Definition PTrcId := Comb.Pos Trace.Pos Identity.Pos.

Definition handleTrace {A B : Type}
                      `{Normalform STrcId PTrcId A B}
                       (p : Free STrcId PTrcId A)
  : (B * list string) :=
  collectMessages (run (runTracing (nf p))).

(* Share :+: Identity handler *)

Definition SShrId := Comb.Shape Share.Shape Identity.Shape.
Definition PShrId := Comb.Pos Share.Pos Identity.Pos.

Definition handleShare {A B : Type}
                       `{Normalform SShrId PShrId A B}
                       (p : Free SShrId PShrId A) : B :=
 run (runEmptySharing (0,0) (nf p)).


(* Two effects *)

(* Share :+: ND :+: Identity handler *)

Definition SShrND := Comb.Shape Share.Shape (Comb.Shape ND.Shape Identity.Shape).
Definition PShrND := Comb.Pos Share.Pos (Comb.Pos ND.Pos Identity.Pos).

Definition handleShareND {A B : Type}
                         `{Normalform SShrND PShrND A B}
                         (p : Free SShrND PShrND A) : (list B) :=
  collectVals (run (runChoice (runNDSharing (0,0) (nf p)))).

(* Share :+: Trace :+: Identity handler *)

Definition SShrTrc := Comb.Shape Share.Shape (Comb.Shape Trace.Shape Identity.Shape).
Definition PShrTrc := Comb.Pos Share.Pos (Comb.Pos Trace.Pos Identity.Pos).

Definition handleShareTrace {A B : Type}
                            `{Normalform SShrTrc PShrTrc A B}
                            (p : Free SShrTrc PShrTrc A)
  : (B * list string) :=
  collectMessages (run (runTracing (runTraceSharing (0,0) (nf p)))).

(* Maybe :+: Share :+: Identity handler *)

Definition SMaybeShr := Comb.Shape Maybe.Shape (Comb.Shape Share.Shape Identity.Shape).
Definition PMaybeShr := Comb.Pos Maybe.Pos (Comb.Pos Share.Pos Identity.Pos).

Definition handleMaybeShare {A B : Type}
                            `{Normalform SMaybeShr PMaybeShr A B}
                            (p : Free SMaybeShr PMaybeShr A) : option B :=
  run (runEmptySharing (0,0) (runMaybe (nf p))).


(* ND :+: Maybe :+: Identity handler *)

Definition SNDMaybe := Comb.Shape ND.Shape (Comb.Shape Maybe.Shape Identity.Shape).
Definition PNDMaybe := Comb.Pos ND.Pos (Comb.Pos Maybe.Pos Identity.Pos).

Definition handleNDMaybe {A B : Type}
                         `{Normalform SNDMaybe PNDMaybe A B}
                         (p : Free SNDMaybe PNDMaybe A)
  : option (list B) := match run (runMaybe (runChoice (nf p))) with
                       | None => None
                       | Some t => Some (collectVals t)
                       end.

(* Maybe :+: Trace :+: Identity handler *)

Definition SMaybeTrc := Comb.Shape Maybe.Shape (Comb.Shape Trace.Shape Identity.Shape).
Definition PMaybeTrc := Comb.Pos Maybe.Pos (Comb.Pos Trace.Pos Identity.Pos).

Definition handleMaybeTrace {A B : Type}
                          `{Normalform SMaybeTrc PMaybeTrc A B}
                          (p : Free SMaybeTrc PMaybeTrc A)
  : option B * list string :=
  collectMessages (run (runTracing (runMaybe (nf p)))).


(* Trace :+: ND :+: Identity handler *)

Definition STrcND := Comb.Shape Trace.Shape (Comb.Shape ND.Shape Identity.Shape).
Definition PTrcND := Comb.Pos Trace.Pos (Comb.Pos ND.Pos Identity.Pos).

Definition handleTraceND {A B : Type}
                         `{Normalform STrcND PTrcND A B}
                         (p : Free STrcND PTrcND A)
  : list (B * list string) :=
  map (@collectMessages B)
                  (@collectVals (B * list (option Sharing.ID * string))
                                (run (runChoice (runTracing (nf p))))).


(* Three effects *)

(* NOTE: There is no handler for an effect stack that contains sharing,
   non-determinism and tracing. This is because only one effect can be
   shared in a program. *)

(* Share :+: ND :+: Maybe :+: Identity handler *)

Definition SShrNDMaybe :=
  Comb.Shape Share.Shape
    (Comb.Shape ND.Shape
      (Comb.Shape Maybe.Shape Identity.Shape)).

Definition PShrNDMaybe :=
  Comb.Pos Share.Pos
    (Comb.Pos ND.Pos
      (Comb.Pos Maybe.Pos Identity.Pos)).

Definition handleShareNDMaybe {A B : Type}
                              `{Normalform SShrNDMaybe PShrNDMaybe A B}
                              (p : Free SShrNDMaybe PShrNDMaybe A)
  : option (list B) :=
  match (run (runMaybe (runChoice (runNDSharing (0,0) (nf p))))) with
  | None   => None
  | Some t => Some (@collectVals B t)
  end.

(* Maybe :+: Share :+: Trace :+: Identity handler *)

Definition SMaybeShrTrc :=
  Comb.Shape Maybe.Shape
    (Comb.Shape Share.Shape
      (Comb.Shape Trace.Shape Identity.Shape)).

Definition PMaybeShrTrc :=
  Comb.Pos Maybe.Pos
    (Comb.Pos Share.Pos
      (Comb.Pos Trace.Pos Identity.Pos)).

Definition handleMaybeShareTrace {A B : Type}
                                 `{Normalform SMaybeShrTrc PMaybeShrTrc A B}
                                 (p : Free SMaybeShrTrc PMaybeShrTrc A)
  : option B * list string :=
  collectMessages (run (runTracing (runTraceSharing (0,0) (runMaybe (nf p))))).


(* ND :+: Maybe :+: Trace :+: Identity handler *)

Definition SNDMaybeTrc :=
  Comb.Shape ND.Shape
    (Comb.Shape Maybe.Shape
      (Comb.Shape Trace.Shape Identity.Shape)).

Definition PNDMaybeTrc :=
  Comb.Pos ND.Pos
    (Comb.Pos Maybe.Pos
      (Comb.Pos Trace.Pos Identity.Pos)).

Definition handleNDMaybeTrc {A B : Type}
                             `{Normalform SNDMaybeTrc PNDMaybeTrc A B}
                             (p : Free SNDMaybeTrc PNDMaybeTrc A)
  : (option (list B) * list string) :=
  let (val,log) := (collectMessages (run (runTracing (runMaybe (runChoice (nf p))))))
  in match val with
     | None => (None, log)
     | Some t => (Some (collectVals t), log)
     end.
