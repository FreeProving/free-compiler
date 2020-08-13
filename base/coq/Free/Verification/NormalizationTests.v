(** * Test module for normalization of effectful programs. *)

From Base Require Import Free.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Instance.Maybe.
From Base Require Import Free.Instance.ND.
From Base Require Import Free.Instance.Trace.
From Base Require Import Prelude.
From Base Require Import Free.Util.Search.

Require Import Lists.List.
Import List.ListNotations.

(* Shortcuts to handle a program. *)

(* Shortcut to evaluate a non-deterministic program to a result list.
   list without normalization. *)
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

(* Lists with effects at the root. *)

(* [] ? [true,false] *)
Definition rootNDList (Shape : Type) (Pos : Shape -> Type) 
                    `{Injectable ND.Shape ND.Pos Shape Pos}
  : Free Shape Pos (List Shape Pos (Bool Shape Pos))
 := Choice Shape Pos
      (Nil Shape Pos)
      (Cons Shape Pos
         (pure true)
         (Cons Shape Pos 
           (pure false)
           (Nil Shape Pos)
         )
      ).
Arguments rootNDList {_} {_} {_}.

(* trace "root effect" [true, false] *)
Definition rootTracedList (Shape : Type) (Pos : Shape -> Type) `{Traceable Shape Pos}
  : Free Shape Pos (List Shape Pos (Bool Shape Pos))
 := trace "root effect"
      (Cons Shape Pos (pure true)
                      (Cons Shape Pos 
                        (pure false) 
                        (Nil Shape Pos)
                      )
      ).
Arguments rootTracedList {_} {_} {_}.


(* Lists with an effectful element. *)

(* [true,true ? false] *)
Definition coinList (Shape : Type) (Pos : Shape -> Type) 
                    `{Injectable ND.Shape ND.Pos Shape Pos}
  : Free Shape Pos (List Shape Pos (Bool Shape Pos))
 := Cons Shape Pos 
      (pure true) 
      (Cons Shape Pos (Choice Shape Pos (pure true) (pure false))
                      (Nil Shape Pos)).
Arguments coinList {_} {_} {_}.

(* [true, trace "component effect" false] *)
Definition traceList (Shape : Type) (Pos : Shape -> Type) `{Traceable Shape Pos}
  : Free Shape Pos (List Shape Pos (Bool Shape Pos))
 := Cons Shape Pos (pure true) 
      (Cons Shape Pos (trace "component effect" (pure false)) (Nil Shape Pos)).
Arguments traceList {_} {_} {_}.

(* [true, undefined] *)
Definition partialList (Shape : Type) (Pos : Shape -> Type) 
                       `(P : Partial Shape Pos)
  : Free Shape Pos (List Shape Pos (Bool Shape Pos))
 := Cons Shape Pos (True_ Shape Pos)
      (Cons Shape Pos undefined (Nil Shape Pos)).
Arguments partialList {_} {_} P.

(* [true, false ? undefined] *)
Definition partialCoinList (Shape : Type) (Pos : Shape -> Type)
                           `{Injectable ND.Shape ND.Pos Shape Pos}
                           `(P : Partial Shape Pos)
  : Free Shape Pos (List Shape Pos (Bool Shape Pos))
 := Cons Shape Pos (True_ Shape Pos)
      (Cons Shape Pos (Choice Shape Pos (False_ Shape Pos) 
                                         undefined) 
                      (Nil Shape Pos)).
Arguments partialCoinList {_} {_} {_} P.

(* List with an effect at the root and an effectful element. *)

(* trace "root effect" [true, trace "component effect" false] *)
Definition tracedTraceList (Shape : Type) (Pos : Shape -> Type) 
                           `{Traceable Shape Pos}
  : Free Shape Pos (List Shape Pos (Bool Shape Pos))
 := trace "root effect" (Cons Shape Pos (pure true) 
      (Cons Shape Pos (trace "component effect" (pure false)) (Nil Shape Pos))).
Arguments tracedTraceList {_} {_} {_}.

(* [] ? [true,true ? false] *)
Definition NDCoinList (Shape : Type) (Pos : Shape -> Type) 
                      `{Injectable ND.Shape ND.Pos Shape Pos}
  : Free Shape Pos (List Shape Pos (Bool Shape Pos))
 := Choice Shape Pos (Nil Shape Pos)
                     (Cons Shape Pos 
                       (pure true) 
                       (Cons Shape Pos 
                         (Choice Shape Pos (pure true) (pure false))
                         (Nil Shape Pos))).
Arguments NDCoinList {_} {_} {_}.

(* Deep effectful components *)

(* [[true, true ? false]] *)
Definition deepCoinList (Shape : Type) (Pos : Shape -> Type) 
                    `{Injectable ND.Shape ND.Pos Shape Pos}
  : Free Shape Pos (List Shape Pos (List Shape Pos (Bool Shape Pos)))
 := Cons Shape Pos
      (Cons Shape Pos 
        (pure true) 
        (Cons Shape Pos (Choice Shape Pos (pure true) (pure false))
                        (Nil Shape Pos)))
      (Nil Shape Pos).
Arguments deepCoinList {_} {_} {_}.

(* [[true, trace "component effect" false]] *)
Definition deepTraceList (Shape : Type) (Pos : Shape -> Type) `{Traceable Shape Pos}
  : Free Shape Pos (List Shape Pos (List Shape Pos (Bool Shape Pos)))
 := Cons Shape Pos
      (Cons Shape Pos 
        (pure true) 
        (Cons Shape Pos (trace "component effect" (pure false)) (Nil Shape Pos)))
      (Nil Shape Pos).
Arguments deepTraceList {_} {_} {_}.

(* A function that is the same as head for non-empty lists.
   Empty lists yield false. *)
Definition headOrFalse (Shape : Type) (Pos : Shape -> Type) 
                       (fl : Free Shape Pos (List Shape Pos (Bool Shape Pos)))
  : Free Shape Pos bool
 := fl >>= fun l => match l with
    | List.nil => pure false
    | List.cons fb _ => fb
    end.
Arguments headOrFalse {_} {_} fl. 

(* Auxiliary properties *)

(* A property that is fulfilled if two lists of Bools are 
   effect-free and contain the same values. *)
Fixpoint pure_equalB (Shape1 : Type) (Pos1 : Shape1 -> Type)
                     (Shape2 : Type) (Pos2 : Shape2 -> Type) 
                     (l1 : List Shape1 Pos1 (Bool Shape1 Pos1))
                     (l2 : List Shape2 Pos2 (Bool Shape2 Pos2))
 : Prop
 := match l1, l2 with
    | List.nil, List.nil => True 
    | (List.cons fx fxs), (List.cons fy fys) => match fx, fxs, fy, fys with
         | (pure x), (pure xs), (pure y), (pure ys) => 
                   x = y /\ pure_equalB Shape1 Pos1 Shape2 Pos2 xs ys
         | _, _, _, _ => False
         end
    | _, _ => False
    end.
Arguments pure_equalB {Shape1} {Pos1} {Shape2} {Pos2} l1 l2.

(* A property that is fulfilled if two traced (handled) lists are effect-free and
   contain the same values. *)
Definition eqTracedList (Shape1 : Type) (Pos1 : Shape1 -> Type)
                        (Shape2 : Type) (Pos2 : Shape2 -> Type) 
                        (e1 : (List Shape1 Pos1 (Bool Shape1 Pos1) * list string))
                        (e2 : (List Shape2 Pos2 (Bool Shape2 Pos2)* list string))
 := match e1 with
    | (l1,log1) => match e2 with
                   | (l2, log2) => log1 = log2 /\ pure_equalB l1 l2
                   end
    end.
Arguments eqTracedList {Shape1} {Pos1} {Shape2} {Pos2} e1 e2.

(* A property that is fulfilled if two non-deterministic (handled) lists are 
   effect-free and contain the same values. *)
Fixpoint eqNDList {Shape1 : Type} {Pos1 : Shape1 -> Type}
                        {Shape2 : Type} {Pos2 : Shape2 -> Type} 
                        (e1 : list (List Shape1 Pos1 (Bool Shape1 Pos1)))
                        (e2 : list (List Shape2 Pos2 (Bool Shape2 Pos2)))
 := match e1, e2 with
    | nil, nil => True
    | (cons l1 l1s), (cons l2 l2s) => pure_equalB l1 l2 /\ eqNDList l1s l2s
    | _, _ => False
    end.

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
   headOrFalse [true, trace "component effect" false] --> (true,[]) *)
Example nonStrictnessNoTracing : evalTracingNF (headOrFalse traceList)
 = (true, []).
Proof. constructor. Qed.

(* Non-strictness should be preserved, so no non-determinism should occur.
   headOrFalse [true,coin] --> [true] *)
Example nonStrictnessNoND : evalNDNF (headOrFalse coinList)
 = [true].
Proof. constructor. Qed.

(* Evaluating the defined part of a partial list is still possible.
   headOrFalse [true,undefined] --> true *)
(* Since Maybe is still handled, the actual result should be Some true. *)
Example nonStrictnessPartiality : evalMaybeNF 
                                    (headOrFalse 
                                      (partialList MaybePartial))
 = Some true.
Proof. constructor. Qed.

(* headOrFalse [true, false ? undefined] --> true *)
(* Since non-determinism and Maybe are still handled, the actual 
   result should be [Some true]. *)
Example nonStrictnessNDPartiality : evalNDMaybeNF 
                                    (headOrFalse 
                                      (partialCoinList MaybePartial))
 = [Some true].
Proof. constructor. Qed.

(* Effects at different levels are accumulated. *)

(* trace "root effect" [true, trace "component effect" false] 
   --> ([true,false], ["root effect", "component effect"])*)
Example rootAndComponentEffectTracing : evalTracingNF tracedTraceList
 = (List.cons (True_ IdS IdP) 
              (List.Cons IdS IdP (False_ IdS IdP) (Nil IdS IdP)),
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
   headOrFalse (trace "root effect" [true, trace "component effect" false])
   --> (true, ["root effect") *)
Example nonStrictnessRootAndComponentTracing 
 : evalTracing (headOrFalse tracedTraceList)
 = (true, ["root effect"%string]).
Proof. constructor. Qed.

(* Only the choice at the root should be triggered. 
   Because the first list is empty and the second has true as its 
   first element, the results should be false and true.
   headOrFalse ([] ? [true, coin]) --> [false,true] *)
Example nonStrictnessRootAndComponentND 
 : evalNDNF (headOrFalse NDCoinList) 
 = [false;true].
Proof. constructor. Qed.

(* Normalization of lists with effects nested deeper inside. *)

(* [[true,trace "component effect" false]]
   --> ([[true,false]],["component effect"]) *)
Example deepEffectTracing : evalTracingNF deepTraceList
 = (List.cons ((List.Cons IdS IdP (True_ IdS IdP) 
                                 (Cons IdS IdP (False_ IdS IdP) 
                                               (Nil IdS IdP)))) 
              (Nil IdS IdP),
    ["component effect"%string]).
Proof. constructor. Qed.

(* [[true, true ? false]] --> [[[true,true]],[[true,false]]] *)
Example deepEffectND : evalNDNF deepCoinList
 = [List.cons ((List.Cons IdS IdP (True_ IdS IdP) 
                                  (Cons IdS IdP (True_ IdS IdP) 
                                                (Nil IdS IdP)))) 
               (Nil IdS IdP);
    List.cons ((List.Cons IdS IdP (True_ IdS IdP) 
                                  (Cons IdS IdP (False_ IdS IdP) 
                                                (Nil IdS IdP)))) 
               (Nil IdS IdP)
].
Proof. constructor. Qed.