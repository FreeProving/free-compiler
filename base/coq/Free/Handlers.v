(** This module contains default handlers for individual effect stacks. *)

From Base Require Import Free.
From Base Require Import Free.Instance.Comb.
From Base Require Import Free.Instance.Error.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Instance.Maybe.
From Base Require Import Free.Instance.ND.
From Base Require Import Free.Instance.Share.
From Base Require Import Free.Instance.Trace.

From Base Require Import Prelude.

From Base Require Import Free.Util.Search.

Require Import Coq.Lists.List.

Section NoEffect.

  (* Identity handler *)
  Instance HandlerNoEffect (A : Type) :
   Handler Identity.Shape Identity.Pos A | 0 := {
    handledType _ := nType;
    handle _ p := run (nf p)
  }.

End NoEffect.

Section OneEffect.

  (* Maybe :+: Identity handler *)

  Definition SMId := Comb.Shape Maybe.Shape Identity.Shape.
  Definition PMId := Comb.Pos Maybe.Pos Identity.Pos.

  Instance HandlerMaybe (A : Type) :
   Handler SMId PMId A | 1 := {
    handle _ p := run (runMaybe (nf p))
  }.

  (* Error :+: Identity handler *)

  Definition SErrId := Comb.Shape (Error.Shape string) Identity.Shape.
  Definition PErrId := Comb.Pos (@Error.Pos string) Identity.Pos.

  Instance HandlerError (A : Type) : Handler SErrId PErrId A  := {
    handle _ p := run (runError (nf p))
  }.


  (* ND :+: Identity handler *)
  Definition SNDId := Comb.Shape ND.Shape Identity.Shape.
  Definition PNDId := Comb.Pos ND.Pos Identity.Pos.

  Instance HandlerND (A : Type) : Handler SNDId PNDId A := {
    handle _ p := collectVals (run (runChoice (nf p)))
  }.

  (* Trace :+: Identity handler *)

  Definition STrcId := Comb.Shape Trace.Shape Identity.Shape.
  Definition PTrcId := Comb.Pos Trace.Pos Identity.Pos.

  Instance HandlerTrace (A : Type) : Handler STrcId PTrcId A := {
    handle _ p := collectMessages (run (runTracing (nf p)))
  }.

  (* Share :+: Identity handler *)

  Definition SShrId := Comb.Shape Share.Shape Identity.Shape.
  Definition PShrId := Comb.Pos Share.Pos Identity.Pos.

  Instance HandlerShare (A : Type) : Handler SShrId PShrId A := {
    handle _ p := (run (runEmptySharing (0,0) (nf p)))
  }.

End OneEffect.

(* NOTE: There is no handler for an effect stack that contains both the Error and
   Maybe effects. Both effects model partiality, but only one interpretation of
   partiality is used at a time. *)

Section TwoEffects.

  (* Share :+: ND :+: Identity handler *)

  Definition SShrND := Comb.Shape Share.Shape (Comb.Shape ND.Shape Identity.Shape).
  Definition PShrND := Comb.Pos Share.Pos (Comb.Pos ND.Pos Identity.Pos).

  Instance HandlerShareND (A : Type) : Handler SShrND PShrND A | 2 := {
    handle _ p := collectVals (run (runChoice (runNDSharing (0,0) (nf p))))
  }.

  (* Share :+: Trace :+: Identity handler *)

  Definition SShrTrc := Comb.Shape Share.Shape (Comb.Shape Trace.Shape Identity.Shape).
  Definition PShrTrc := Comb.Pos Share.Pos (Comb.Pos Trace.Pos Identity.Pos).

  Instance HandlerShareTrace (A : Type) : Handler SShrTrc PShrTrc A | 2 := {
    handle _ p := collectMessages (run (runTracing (runTraceSharing (0,0) (nf p))))
  }.

  (* Share :+: Maybe :+: Identity handler *)

  Definition SShrMaybe := Comb.Shape Share.Shape (Comb.Shape Maybe.Shape Identity.Shape).
  Definition PShrMaybe := Comb.Pos Share.Pos (Comb.Pos Maybe.Pos Identity.Pos).

  Instance HandlerShareMaybe (A : Type) : Handler SShrMaybe PShrMaybe A | 2 := {
   handle _ p := run (runMaybe (runEmptySharing (0,0) (nf p)))
  }.

  (* ND :+: Maybe :+: Identity handler *)

  Definition SNDMaybe := Comb.Shape ND.Shape (Comb.Shape Maybe.Shape Identity.Shape).
  Definition PNDMaybe := Comb.Pos ND.Pos (Comb.Pos Maybe.Pos Identity.Pos).

  Instance HandlerNDMaybe (A : Type) : Handler SNDMaybe PNDMaybe A | 2 := {
   handledType _ := option (list nType);
   handle _ p := match run (runMaybe (runChoice (nf p))) with
                 | None => None
                 | Some t => Some (collectVals t)
                 end
  }.

  (* Maybe :+: Trace :+: Identity handler *)

  Definition SMaybeTrc := Comb.Shape Maybe.Shape (Comb.Shape Trace.Shape Identity.Shape).
  Definition PMaybeTrc := Comb.Pos Maybe.Pos (Comb.Pos Trace.Pos Identity.Pos).

  Instance HandlerMaybeTrace (A : Type) : Handler SMaybeTrc PMaybeTrc A | 2 := {
   handle _ p := collectMessages (run (runTracing (runMaybe (nf p))))
  }.

  (* Share :+: Error :+: Identity handler *)

  Definition SShrErr := Comb.Shape Share.Shape (Comb.Shape (Error.Shape string) Identity.Shape).
  Definition PShrErr := Comb.Pos Share.Pos (Comb.Pos (@Error.Pos string) Identity.Pos).

  Instance HandlerShareError (A : Type) : Handler SShrErr PShrErr A | 2 := {
   handle _ p := run (runError (runEmptySharing (0,0) (nf p)))
  }.

  (* ND :+: Error :+: Identity handler *)

  Definition SNDErr := Comb.Shape ND.Shape (Comb.Shape (Error.Shape string) Identity.Shape).
  Definition PNDErr := Comb.Pos ND.Pos (Comb.Pos (@Error.Pos string)  Identity.Pos).

  Instance HandlerNDError (A : Type) : Handler SNDErr PNDErr A := {
   handledType _ := sum (list nType) string;
   handle _ p := match run (runError (runChoice (nf p))) with
                 | inl t => inl (collectVals t)
                 | inr e => inr e
                 end
  }.

  (* Error :+: Trace :+: Identity handler *)
  (* In Haskell, when an error is thrown in a traced program, the message log until that point
     is displayed alongside the error message.
     Therefore, the error effect is handled before the tracing effect. *)

  Definition SErrorTrc := Comb.Shape (Error.Shape string) (Comb.Shape Trace.Shape Identity.Shape).
  Definition PErrorTrc := Comb.Pos (@Error.Pos string) (Comb.Pos Trace.Pos Identity.Pos).

  Instance HandlerErrorTrc (A : Type) : Handler SErrorTrc PErrorTrc A := {
   handle _ p := collectMessages (run (runTracing (runError (nf p))))
  }.

  (* Trace :+: ND :+: Identity handler *)

  Definition STrcND := Comb.Shape Trace.Shape (Comb.Shape ND.Shape Identity.Shape).
  Definition PTrcND := Comb.Pos Trace.Pos (Comb.Pos ND.Pos Identity.Pos).

  Instance HandlerTraceND (A : Type) : Handler STrcND PTrcND A := {
    handle _ p := map (@collectMessages nType)
                      (@collectVals (nType * list (option Sharing.ID * string))
                                    (run (runChoice (runTracing (nf p)))))
  }.

End TwoEffects.

Section ThreeEffects.

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

  Instance HandlerShareNDMaybe (A : Type) : Handler SShrNDMaybe PShrNDMaybe A | 3 := {
   handledType _ := option (list nType);
   handle _ p := match (run (runMaybe (runChoice (runNDSharing (0,0) (nf p))))) with
                 | None   => None
                 | Some t => Some (@collectVals nType t)
                 end
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

  Instance HandlerMaybeShareTrace (A : Type) : Handler SMaybeShrTrc PMaybeShrTrc A := {
   handle _ p := collectMessages (run (runTracing (runTraceSharing (0,0) (runMaybe (nf p)))))
  }.

  (* ND :+: Maybe :+: Trace :+: Identity handler *)

  Definition SNDMaybeTrc :=
    Comb.Shape ND.Shape
      (Comb.Shape Maybe.Shape
        (Comb.Shape Trace.Shape Identity.Shape)).

  Definition PNDMaybeTrc :=
    Comb.Pos ND.Pos
      (Comb.Pos Maybe.Pos
        (Comb.Pos Trace.Pos Identity.Pos)).

  Instance HandlerNDMaybeTrc (A : Type) (p : Free SNDMaybeTrc PNDMaybeTrc A)
    : Handler SNDMaybeTrc PNDMaybeTrc A := {
   handle _ p := let (val,log) := (collectMessages (run (runTracing (runMaybe (runChoice (nf p))))))
                 in match val with
                    | None => (None, log)
                    | Some t => (Some (collectVals t), log)
                    end
  }.

  (* Share :+: ND :+: Error :+: Identity handler *)

  Definition SShrNDErr :=
    Comb.Shape Share.Shape
      (Comb.Shape ND.Shape
        (Comb.Shape (Error.Shape string) Identity.Shape)).

  Definition PShrNDErr :=
    Comb.Pos Share.Pos
      (Comb.Pos ND.Pos
        (Comb.Pos (@Error.Pos string) Identity.Pos)).

  Instance HandlerShareNDError (A : Type) : Handler SShrNDErr PShrNDErr A := {
   handledType _ := sum (list nType) string;
   handle _ p := match run (runError (runChoice (runNDSharing (0,0) (nf p)))) with
                 | inl t => inl (collectVals t)
                 | inr e => inr e
                 end
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

  Instance HandlerErrorShareTrace (A : Type) : Handler SErrShrTrc PErrShrTrc A := {
   handle _ p := collectMessages (run (runTracing (runTraceSharing (0,0) (runError (nf p)))))
  }.

  (* ND :+: Error :+: Trace :+: Identity handler *)

  Definition SNDErrTrc :=
    Comb.Shape ND.Shape
      (Comb.Shape (Error.Shape string)
        (Comb.Shape Trace.Shape Identity.Shape)).

  Definition PNDErrTrc :=
    Comb.Pos ND.Pos
      (Comb.Pos (@Error.Pos string)
        (Comb.Pos Trace.Pos Identity.Pos)).

  Instance HandlerNDErrorTrace (A : Type) : Handler SNDErrTrc PNDErrTrc A := {
   handledType _ := prod (sum (list nType) string) (list string);
   handle _ p := match collectMessages (run (runTracing (runError (runChoice (nf p)))))
                 with
                 | (inl t, log) => (inl (collectVals t), log)
                 | (inr e, log) => (inr e, log)
                 end
  }.

End ThreeEffects.

Section AnyEffects.

  (* A dummy handler to forego handling in theorems with a concrete
     effect stack. *)
  Instance NoHandler (Shape : Type) (Pos : Shape -> Type) (A : Type) : Handler Shape Pos A := {
   handle _ p := p
  }.

End AnyEffects.
