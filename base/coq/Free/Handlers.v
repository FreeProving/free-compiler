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

From Base Require Import Free.Util.All.
From Base Require Import Free.Util.Search.

Require Import Coq.Lists.List.

Instance PropNF (Shape : Type) (Pos : Shape -> Type) : Normalform Shape Pos Prop
 := { nf' x := pure x }.

Section NoEffect.

  (* Identity handler *)
  Instance HandlerNoEffect :
   Handler Identity.Shape Identity.Pos | 0 := {
    handledType _ _ := nType;
    handle _ _ fx := run (nf fx);
    handleProp fx := run (nf fx)
  }.

End NoEffect.

Section OneEffect.

  (* Maybe :+: Identity handler *)

  Definition SMId := Comb.Shape Maybe.Shape Identity.Shape.
  Definition PMId := Comb.Pos Maybe.Pos Identity.Pos.

  Instance HandlerMaybe :
   Handler SMId PMId | 1 := {
    handle _ _ fx := run (runMaybe (nf fx));
    handleProp fx := run (runMaybeProp (nf fx))
  }.

  (* Error :+: Identity handler *)

  Definition SErrId := Comb.Shape (Error.Shape string) Identity.Shape.
  Definition PErrId := Comb.Pos (@Error.Pos string) Identity.Pos.

  Instance HandlerError : Handler SErrId PErrId := {
    handle _ _ fx := run (runError (nf fx));
    handleProp fx := run (runErrorProp (nf fx))
  }.

  (* ND :+: Identity handler *)
  Definition SNDId := Comb.Shape ND.Shape Identity.Shape.
  Definition PNDId := Comb.Pos ND.Pos Identity.Pos.

  Instance HandlerND : Handler SNDId PNDId := {
    handle _ _ fx := collectVals (run (runChoice (nf fx)));

    (* When proving properties about non-deterministic computations, consider
       a property as true only if the property constructed by every branch
       of the computation is satisfied. *)
    handleProp fx := all (collectVals (run (runChoice (nf fx))))
  }.

  (* Trace :+: Identity handler *)

  Definition STrcId := Comb.Shape Trace.Shape Identity.Shape.
  Definition PTrcId := Comb.Pos Trace.Pos Identity.Pos.

  Instance HandlerTrace : Handler STrcId PTrcId := {
    handle _ _ fx := collectMessages (run (runTracing (nf fx)));

    (* If messages are logged during the construction of a property, discard
       the messages and prove just prove the constructed property. *)
    handleProp fx := discardMessages (run (runTracing (nf fx)))
  }.

  (* Share :+: Identity handler *)

  Definition SShrId := Comb.Shape Share.Shape Identity.Shape.
  Definition PShrId := Comb.Pos Share.Pos Identity.Pos.

  Instance HandlerShare : Handler SShrId PShrId := {
    handle _ _ fx := run (runEmptySharing (0,0) (nf fx));

    (* Even in the presence of sharing, the construction of an otherwise pure
       property can never fail. *)
    handleProp fx := run (runEmptySharing (0,0) (nf fx))
  }.

End OneEffect.

(* NOTE: There is no handler for an effect stack that contains both the Error and
   Maybe effects. Both effects model partiality, but only one interpretation of
   partiality is used at a time. *)

Section TwoEffects.

  (* Share :+: ND :+: Identity handler *)

  Definition SShrND := Comb.Shape Share.Shape (Comb.Shape ND.Shape Identity.Shape).
  Definition PShrND := Comb.Pos Share.Pos (Comb.Pos ND.Pos Identity.Pos).

  Instance HandlerShareND : Handler SShrND PShrND | 2 := {
    handle _ _ fx := collectVals (run (runChoice (runNDSharing (0,0) (nf fx))));
    handleProp fx := all (collectVals (run (runChoice (runNDSharing (0,0) (nf fx)))))
  }.

  (* Share :+: Trace :+: Identity handler *)

  Definition SShrTrc := Comb.Shape Share.Shape (Comb.Shape Trace.Shape Identity.Shape).
  Definition PShrTrc := Comb.Pos Share.Pos (Comb.Pos Trace.Pos Identity.Pos).

  Instance HandlerShareTrace : Handler SShrTrc PShrTrc | 2 := {
    handle _ _ fx := collectMessages (run (runTracing (runTraceSharing (0,0) (nf fx))));
    handleProp fx := discardMessages (run (runTracing (runTraceSharing (0,0) (nf fx))));
  }.

  (* Share :+: Maybe :+: Identity handler *)

  Definition SShrMaybe := Comb.Shape Share.Shape (Comb.Shape Maybe.Shape Identity.Shape).
  Definition PShrMaybe := Comb.Pos Share.Pos (Comb.Pos Maybe.Pos Identity.Pos).

  Instance HandlerShareMaybe : Handler SShrMaybe PShrMaybe | 2 := {
   handle _ _ fx := run (runMaybe (runEmptySharing (0,0) (nf fx)));
   handleProp fx := run (runMaybeProp (runEmptySharing (0,0) (nf fx)))
  }.

  (* ND :+: Maybe :+: Identity handler *)

  Definition SNDMaybe := Comb.Shape ND.Shape (Comb.Shape Maybe.Shape Identity.Shape).
  Definition PNDMaybe := Comb.Pos ND.Pos (Comb.Pos Maybe.Pos Identity.Pos).

  Instance HandlerNDMaybe : Handler SNDMaybe PNDMaybe | 2 := {
   handledType _ _ := option (list nType);
   handle _ _ fx := match run (runMaybe (runChoice (nf fx))) with
                    | None => None
                    | Some x => Some (collectVals x)
                    end;

   (* When proving a property whose construction involves partiality and
      non-determinism, the property is considered to be false when the
      construction failed but true if the computation does not have any
      branch. If there are branches, all properties produced in all braches
      must be satisfied. *)
   handleProp fx := match run (runMaybe (runChoice (nf fx))) with
                    | None   => False
                    | Some x => all (collectVals x)
                    end
  }.

  (* Maybe :+: Trace :+: Identity handler *)

  Definition SMaybeTrc := Comb.Shape Maybe.Shape (Comb.Shape Trace.Shape Identity.Shape).
  Definition PMaybeTrc := Comb.Pos Maybe.Pos (Comb.Pos Trace.Pos Identity.Pos).

  Instance HandlerMaybeTrace : Handler SMaybeTrc PMaybeTrc | 2 := {
   handle _ _ fx := collectMessages (run (runTracing (runMaybe (nf fx))));
   handleProp fx := discardMessages (run (runTracing (runMaybeProp (nf fx))))
  }.

  (* Share :+: Error :+: Identity handler *)

  Definition SShrErr := Comb.Shape Share.Shape (Comb.Shape (Error.Shape string) Identity.Shape).
  Definition PShrErr := Comb.Pos Share.Pos (Comb.Pos (@Error.Pos string) Identity.Pos).

  Instance HandlerShareError : Handler SShrErr PShrErr | 2 := {
   handle _ _ fx := run (runError (runEmptySharing (0,0) (nf fx)));
   handleProp fx := run (runErrorProp (runEmptySharing (0,0) (nf fx)))
  }.

  (* ND :+: Error :+: Identity handler *)

  Definition SNDErr := Comb.Shape ND.Shape (Comb.Shape (Error.Shape string) Identity.Shape).
  Definition PNDErr := Comb.Pos ND.Pos (Comb.Pos (@Error.Pos string)  Identity.Pos).

  Instance HandlerNDError : Handler SNDErr PNDErr := {
   handledType _ _ := sum (list nType) string;
   handle _ _ fx := match run (runError (runChoice (nf fx))) with
                    | inl x => inl (collectVals x)
                    | inr e => inr e
                    end;
   handleProp fx := match run (runError (runChoice (nf fx))) with
                    | inl x => all (collectVals x)
                    | inr _ => False
                    end
  }.

  (* Error :+: Trace :+: Identity handler *)
  (* In Haskell, when an error is thrown in a traced program, the message log until that point
     is displayed alongside the error message.
     Therefore, the error effect is handled before the tracing effect. *)

  Definition SErrorTrc := Comb.Shape (Error.Shape string) (Comb.Shape Trace.Shape Identity.Shape).
  Definition PErrorTrc := Comb.Pos (@Error.Pos string) (Comb.Pos Trace.Pos Identity.Pos).

  Instance HandlerErrorTrace (A : Type) : Handler SErrorTrc PErrorTrc := {
   handle _ _ fx := collectMessages (run (runTracing (runError (nf fx))));
   handleProp fx := discardMessages (run (runTracing (runErrorProp (nf fx))))
  }.

  (* Trace :+: ND :+: Identity handler *)

  Definition STrcND := Comb.Shape Trace.Shape (Comb.Shape ND.Shape Identity.Shape).
  Definition PTrcND := Comb.Pos Trace.Pos (Comb.Pos ND.Pos Identity.Pos).

  Instance HandlerTraceND : Handler STrcND PTrcND := {
    handle _ _ fx := map (@collectMessages nType)
                         (@collectVals (nType * list (option Sharing.ID * string))
                                       (run (runChoice (runTracing (nf fx)))));
    handleProp fx := all (map (@discardMessages nType)
                              (@collectVals (nType * list (option Sharing.ID * string))
                                   (run (runChoice (runTracing (nf fx))))))
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

  Instance HandlerShareNDMaybe : Handler SShrNDMaybe PShrNDMaybe | 3 := {
   handledType _ _ := option (list nType);
   handle _ _ fx := match (run (runMaybe (runChoice (runNDSharing (0,0) (nf fx))))) with
                 | None   => None
                 | Some t => Some (@collectVals nType t)
                 end;
   handleProp fx := match (run (runMaybe (runChoice (runNDSharing (0,0) (nf fx))))) with
                 | None   => False
                 | Some t => all (@collectVals nType t)
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

  Instance HandlerMaybeShareTrace : Handler SMaybeShrTrc PMaybeShrTrc := {
   handle _ _ fx := collectMessages (run (runTracing (runTraceSharing (0,0) (runMaybe (nf fx)))));
   handleProp fx := discardMessages (run (runTracing (runTraceSharing (0,0) (runMaybeProp (nf fx)))))
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

  Instance HandlerNDMaybeTrace : Handler SNDMaybeTrc PNDMaybeTrc := {
   handle _ _ fx := let (val,log) := (collectMessages (run (runTracing (runMaybe (runChoice (nf fx))))))
                    in match val with
                       | None => (None, log)
                       | Some x => (Some (collectVals x), log)
                       end;
   handleProp fx := match discardMessages (run (runTracing (runMaybe (runChoice (nf fx))))) with
                    | None   => False
                    | Some x => all (collectVals x)
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

  Instance HandlerShareNDError : Handler SShrNDErr PShrNDErr := {
   handledType _ _ := sum (list nType) string;
   handle _ _ fx := match run (runError (runChoice (runNDSharing (0,0) (nf fx)))) with
                    | inl x => inl (collectVals x)
                    | inr e => inr e
                    end;
   handleProp fx := match run (runError (runChoice (runNDSharing (0,0) (nf fx)))) with
                    | inl x => all (collectVals x)
                    | inr _ => False
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

  Instance HandlerErrorShareTrace : Handler SErrShrTrc PErrShrTrc := {
   handle _ _ fx := collectMessages (run (runTracing (runTraceSharing (0,0) (runError (nf fx)))));
   handleProp fx := discardMessages (run (runTracing (runTraceSharing (0,0) (runErrorProp (nf fx)))))
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

  Instance HandlerNDErrorTrace : Handler SNDErrTrc PNDErrTrc := {
   handledType _ _ := prod (sum (list nType) string) (list string);
   handle _ _ fx := match collectMessages (run (runTracing (runError (runChoice (nf fx))))) with
                    | (inl t, log) => (inl (collectVals t), log)
                    | (inr e, log) => (inr e, log)
                    end;
   handleProp fx := match discardMessages (run (runTracing (runError (runChoice (nf fx))))) with
                    | inl x => all (collectVals x)
                    | inr _ => False
                    end
  }.

End ThreeEffects.

Section AnyEffects.

  (* A dummy handler to forego handling in theorems with a concrete
     effect stack. *)
  Instance NoHandler (Shape : Type) (Pos : Shape -> Type) : Handler Shape Pos := {
   handle _ _ fx := fx;

   (* By default, the construction of a property must yield a pure value. *)
   handleProp fx := match fx with
                    | pure x => x
                    | impure _ _ => False
                    end
  }.

End AnyEffects.
