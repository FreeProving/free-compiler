(** * Test module for normalization of effectful programs. *)

From Base Require Import Free.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Instance.Maybe.
From Base Require Import Free.Instance.ND.
From Base Require Import Free.Instance.Trace.
From Base Require Import Prelude.
From Base Require Import Free.Util.Search.

From Generated Require Data.List.
From Generated Require Data.Tuple.

Require Import Lists.List.
Import List.ListNotations.

(* Shortcuts to handle a program. *)

(* Shortcut to evaluate a non-deterministic program to a result list
   without normalization. *)
Definition evalND {A : Type} (p : Free _ _ A)
:= @collectVals A (run (runChoice p)).

(* Shortcut to evaluate a traced program to a result and a list of logged 
   messages without normalization. *)
Definition evalTracing {A : Type} p 
:= @collectMessages A (run (runTracing p)).

(* Shortcut to evaluate a program with partial values to an option. *)
Definition evalMaybe {A : Type} p
:= run (@runMaybe A _ _ p).

(* Shortcut to evaluate a program with partiality and non-determinism. *)
Definition evalNDMaybe {A : Type} p
:= @evalND (option A) (runMaybe p).

(* Handle a non-deterministic program after normalization. *)
Definition evalNDNF {A B : Type} 
                    `{Normalform _ _ A B}
  p := evalND (nf p).

(* Handle a traced program after normalization. *)
Definition evalTracingNF {A B : Type} 
                         `{Normalform _ _ A B} p
  := evalTracing (nf p).

(* Handle a traced program after normalization. *)
Definition evalTracingMaybeNF {A B : Type} 
                         `{Normalform _ _ A B} p
  := evalTracing (runMaybe (nf p)).

(* Handle a possibly partial program after normalization. *)
Definition evalMaybeNF {A B : Type} 
                       `{Normalform _ _ A B} p
  := evalMaybe (nf p).

(* Handle a possibly partial or non-deterministic program after 
   normalization. *)
Definition evalNDMaybeNF {A B : Type}
                         `{Normalform _ _ A B} p 
:= evalNDMaybe (nf p).

(* Shortcuts for the Identity effect (i.e. the lack of an effect). *)
Definition IdS := Identity.Shape.
Definition IdP := Identity.Pos.

Definition MaybePartial (Shape : Type) (Pos : Shape -> Type)
                        `{Injectable Maybe.Shape Maybe.Pos Shape Pos}
 := PartialLifted Maybe.Shape Maybe.Pos Shape Pos Maybe.Partial.
Arguments MaybePartial {_} {_} {_}.

(* Effectful lists *)
Section SecData.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.

  Notation "'FreeBoolList'" := (Free Shape Pos (List Shape Pos (Bool Shape Pos))).
  Notation "'ND'" := (Injectable ND.Shape ND.Pos Shape Pos).
  Notation "'Trace'" := (Traceable Shape Pos).
  Notation "'Partial'" := (Partial Shape Pos).
  Notation "'FreeBoolListList'" := (Free Shape Pos (List Shape Pos (List Shape Pos (Bool Shape Pos)))).

  (* Lists with effects at the root. *)

  (* [] ? [true,false] *)
  Definition rootNDList `{ND} : FreeBoolList
  := Choice Shape Pos
        (Nil Shape Pos)
        (Cons Shape Pos
           (pure true)
           (Cons Shape Pos 
             (pure false)
             (Nil Shape Pos)
           )
        ).

  (* trace "root effect" [true, false] *)
  Definition rootTracedList `{Trace} : FreeBoolList
  := trace "root effect"
        (Cons Shape Pos (pure true)
                        (Cons Shape Pos 
                            (pure false) 
                            (Nil Shape Pos))).

  (* Lists with an effectful element. *)

  (* [true,true ? false] *)
  Definition coinList `{ND} : FreeBoolList
   := Cons Shape Pos 
        (pure true) 
        (Cons Shape Pos (Choice Shape Pos (pure true) (pure false))
                        (Nil Shape Pos)).

  (* [true, trace "component effect" false] *)
  Definition traceList `{Trace} : FreeBoolList
   := Cons Shape Pos (pure true) 
                     (Cons Shape Pos (trace "component effect" (pure false)) 
                                     (Nil Shape Pos)).

  (* [true, undefined] *)
  Definition partialList `(Partial) : FreeBoolList
   := Cons Shape Pos (True_ Shape Pos)
        (Cons Shape Pos undefined (Nil Shape Pos)).

  (* [true, false ? undefined] *)
  Definition partialCoinList `{ND} `(Partial) : FreeBoolList
   := Cons Shape Pos (True_ Shape Pos)
        (Cons Shape Pos (Choice Shape Pos (False_ Shape Pos) 
                                           undefined) 
                        (Nil Shape Pos)).

  (* List with an effect at the root and an effectful element. *)

  (* trace "root effect" [true, trace "component effect" false] *)
  Definition tracedTraceList `{Trace} : FreeBoolList
   := trace "root effect" 
        (Cons Shape Pos (pure true) 
                        (Cons Shape Pos (trace "component effect" (pure false))
                                        (Nil Shape Pos))).

  (* [] ? [true,true ? false] *)
  Definition NDCoinList `{ND} : FreeBoolList
   := Choice Shape Pos (Nil Shape Pos)
                       (Cons Shape Pos 
                           (pure true) 
                           (Cons Shape Pos 
                               (Choice Shape Pos (pure true) (pure false))
                               (Nil Shape Pos))).

  (* Deep effectful components *)

  (* [[true, true ? false]] *)
  Definition deepCoinList `{ND} : FreeBoolListList
   := Cons Shape Pos
        (Cons Shape Pos 
          (pure true) 
          (Cons Shape Pos (Choice Shape Pos (pure true) (pure false))
                          (Nil Shape Pos)))
        (Nil Shape Pos).

  (* [[true, trace "component effect" false]] *)
  Definition deepTraceList `{Trace} : FreeBoolListList
   := Cons Shape Pos
        (Cons Shape Pos 
            (pure true) 
            (Cons Shape Pos (trace "component effect" (pure false)) 
                            (Nil Shape Pos)))
        (Nil Shape Pos).

End SecData.

(* Arguments sentences for the effectful lists. *)
Arguments rootNDList {_} {_} {_}.
Arguments coinList {_} {_} {_}.
Arguments rootTracedList {_} {_} {_}.
Arguments traceList {_} {_} {_}.
Arguments partialList {_} {_} _.
Arguments partialCoinList {_} {_} {_} _.
Arguments tracedTraceList {_} {_} {_}.
Arguments NDCoinList {_} {_} {_}.
Arguments deepCoinList {_} {_} {_}.
Arguments deepTraceList {_} {_} {_}.

(* Section for auxiliary properties *)
Section SecProps.

  Variable Shape1 : Type.
  Variable Shape2 : Type.
  Variable Pos1 : Shape1 -> Type.
  Variable Pos2 : Shape2 -> Type.

  Notation "'BoolList1'" := (List Shape1 Pos1 (Bool Shape1 Pos1)).
  Notation "'BoolList2'" := (List Shape2 Pos2 (Bool Shape2 Pos2)).

  (* A property that is fulfilled if two lists of Bools are 
     effect-free and contain the same values. *)
  Fixpoint pure_equalB (l1 : BoolList1) (l2 : BoolList2) : Prop
   := match l1, l2 with
      | List.nil, List.nil => True 
      | (List.cons fx fxs), (List.cons fy fys) => match fx, fxs, fy, fys with
           | (pure x), (pure xs), (pure y), (pure ys) => 
                     x = y /\ pure_equalB xs ys
           | _, _, _, _ => False
           end
      | _, _ => False
      end.

  (* A property that is fulfilled if two traced (handled) lists are effect-free and
     contain the same values. *)
  Definition eqTracedList (e1 : BoolList1 * list string)
                          (e2 : BoolList2 * list string)
   := match e1 with
      | (l1,log1) => match e2 with
                     | (l2, log2) => log1 = log2 /\ pure_equalB l1 l2
                     end
      end.

  (* A property that is fulfilled if two non-deterministic (handled) lists are 
     effect-free and contain the same values. *)
  Fixpoint eqNDList (e1 : list BoolList1) (e2 : list BoolList2)
   := match e1, e2 with
      | nil, nil => True
      | (cons l1 l1s), (cons l2 l2s) => pure_equalB l1 l2 /\ eqNDList l1s l2s
      | _, _ => False
      end.

End SecProps.

(* Arguments sentences for the properties. *)
Arguments pure_equalB {_} {_} {_} {_} _ _.
Arguments eqTracedList {_} {_} {_} {_} _ _.
Arguments eqNDList {_} {_} {_} {_} _ _.


(* A property that is fulfilled if a list contains at least one 
   impure component. *)
Fixpoint list_is_impure (Shape : Type) (Pos : Shape -> Type)
                      {A : Type} (l : List Shape Pos A)
 : Prop := match l with
           | List.nil => False
           | List.cons fx fxs => match fx, fxs with
                                 | (pure _), (pure xs) => list_is_impure _ _ xs
                                 | _, _ => True
                                 end
           end.


(* Test cases *)

(* When there are only effects at the root of the list, normalization
   does not change the result and the result only contains pure values.
   Only the effect stack is changed, but since the result only contains pure
   values, the effect stack is irrelevant. *)
Example rootEffectTracing : eqTracedList (evalTracing rootTracedList)
                                         (evalTracingNF rootTracedList).
Proof. repeat (split || reflexivity). Qed.

Example rootEffectND : eqNDList (evalND rootNDList) (evalNDNF rootNDList).
Proof. repeat (split || reflexivity). Qed.

(* Handling tracing in a list without normalization causes 
   the result to still contain 'impure', i.e. the component effects are not
   handled. *)
Example componentsUnhandledTracing 
 : list_is_impure _ _ (fst (evalTracing traceList)).
Proof. easy. Qed.

(* Handling non-determinism in a list without normalization causes 
   the result to still contain 'impure', i.e. the component effects are not 
   handled. *)
Example componentsUnhandledND
 : list_is_impure _ _ (hd (List.nil) (evalND coinList)).
Proof. easy. Qed.

(* Normalization of lists with an effectful element. *)

(* [true, trace "compoment effect" false]
   --> ([true,false],["component effect"]*)
Example componentEffectTracing : evalTracingNF traceList =
  ((List.cons (True_ IdS IdP) (Cons IdS IdP (False_ IdS IdP) (Nil IdS IdP))),
   ["component effect"%string]).
Proof. constructor. Qed.

(* [true, coin] --> [[true,true], [true,false]] *)
Example componentEffectND : evalNDNF coinList
 = [(List.cons (True_ IdS IdP) (Cons IdS IdP (True_ IdS IdP) (Nil IdS IdP)));
    (List.cons (True_ IdS IdP) (Cons IdS IdP (False_ IdS IdP) (Nil IdS IdP)))].
Proof. constructor. Qed.

(* [true, undefined] --> undefined *)
Example componentEffectPartial : evalMaybeNF (partialList MaybePartial)
 = None.
Proof. constructor. Qed.

(* [true, false ? undefined] --> [[true,false], undefined] *)
Example componentEffectPartialND : evalNDMaybeNF (partialCoinList MaybePartial)
 = [Some (List.cons (True_ IdS IdP) (Cons IdS IdP (False_ IdS IdP) (Nil IdS IdP)));
    None].
Proof. constructor. Qed.

(* Normalization combined with non-strictness. *)

(* Non-strictness should be preserved, so no tracing should occur.
   head _ _ MaybePartial [true, trace "component effect" false] --> (true,[]) *)
Example nonStrictnessNoTracing : evalTracingMaybeNF (List.head _ _ MaybePartial traceList)
 = (Some true, []).
Proof. constructor. Qed.

(* Non-strictness should be preserved, so no non-determinism should occur.
   head [true,coin] --> [true] *)
Example nonStrictnessNoND : evalNDMaybeNF (List.head _ _ MaybePartial coinList)
 = [Some true].
Proof. constructor. Qed.

(* Evaluating the defined part of a partial list is still possible.
   head [true,undefined] --> true *)
(* Since Maybe is still handled, the actual result should be Some true. *)
Example nonStrictnessPartiality : evalMaybeNF 
                                    (List.head _ _ MaybePartial 
                                      (partialList MaybePartial))
 = Some true.
Proof. constructor. Qed.

(* head _ _ MaybePartial [true, false ? undefined] --> true *)
(* Since non-determinism and Maybe are still handled, the actual 
   result should be [Some true]. *)
Example nonStrictnessNDPartiality : evalNDMaybeNF 
                                    (List.head _ _ MaybePartial 
                                      (partialCoinList MaybePartial))
 = [Some true].
Proof. constructor. Qed.

(* Effects at different levels are accumulated. *)

(* trace "root effect" [true, trace "component effect" false] 
   --> ([true,false], ["root effect", "component effect"])*)
Example rootAndComponentEffectTracing : evalTracingNF tracedTraceList
 = (List.cons (True_ IdS IdP) 
              (Cons IdS IdP (False_ IdS IdP) (Nil IdS IdP)),
    ["root effect"%string; "component effect"%string]).
Proof. constructor. Qed.

(* [] ? [true, coin] --> [[], [true,true], [true,false]] *)
Example rootAndComponentEffectND : evalNDNF NDCoinList
 = [List.nil;
   (List.cons (True_ IdS IdP) (Cons IdS IdP (True_ IdS IdP) (Nil IdS IdP)));
   (List.cons (True_ IdS IdP) (Cons IdS IdP (False_ IdS IdP) (Nil IdS IdP)))].
Proof. constructor. Qed.

(* Combining non-strictness with effects at different levels. *)

(* Only the message at the root should be logged. 
   head _ _ MaybePartial (trace "root effect" [true, trace "component effect" false])
   --> (true, ["root effect") *)
Example nonStrictnessRootAndComponentTracing 
 : evalTracingMaybeNF (List.head _ _ MaybePartial tracedTraceList)
 = (Some true, ["root effect"%string]).
Proof. constructor. Qed.

(* Only the choice at the root should be triggered. 
   Because the first list is empty and the second has true as its 
   first element, the results should be false and true.
   head ([] ? [true, coin]) --> [undefined,true] *)
Example nonStrictnessRootAndComponentND 
 : evalNDMaybeNF (List.head _ _ MaybePartial NDCoinList) 
 = [None; Some true].
Proof. constructor. Qed.

(* Normalization of lists with effects nested deeper inside. *)

(* [[true,trace "component effect" false]]
   --> ([[true,false]],["component effect"]) *)
Example deepEffectTracing : evalTracingNF deepTraceList
 = (List.cons ((Cons IdS IdP (True_ IdS IdP) 
                                 (Cons IdS IdP (False_ IdS IdP) 
                                               (Nil IdS IdP)))) 
              (Nil IdS IdP),
    ["component effect"%string]).
Proof. constructor. Qed.

(* [[true, true ? false]] --> [[[true,true]],[[true,false]]] *)
Example deepEffectND : evalNDNF deepCoinList
 = [List.cons ((Cons IdS IdP (True_ IdS IdP) 
                                  (Cons IdS IdP (True_ IdS IdP) 
                                                (Nil IdS IdP)))) 
               (Nil IdS IdP);
    List.cons ((Cons IdS IdP (True_ IdS IdP) 
                                  (Cons IdS IdP (False_ IdS IdP) 
                                                (Nil IdS IdP)))) 
               (Nil IdS IdP)
].
Proof. constructor. Qed.
