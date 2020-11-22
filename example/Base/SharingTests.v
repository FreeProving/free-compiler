(** * Test module for sharing handlers. *)

From Base Require Import Free.
From Base Require Import Free.Handlers.
From Base Require Import Free.Instance.Comb.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Instance.Maybe.
From Base Require Import Free.Instance.ND.
From Base Require Import Free.Instance.Share.
From Base Require Import Free.Instance.Trace.

From Base Require Import Free.Util.Search.

From Generated Require Data.List.
From Generated Require Data.Tuple.

From Base Require Import Prelude.
Open Scope string_scope.

Require Import Lists.List.
Import List.ListNotations.

Section SecData.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Variable S : Strategy Shape Pos.
  Variable A : Type.
  Context `{ShareableArgs Shape Pos A}.

  (* Infer Shape and Pos when tracing for convenience. *)
  Arguments trace {_} {_} {_} {_}.

  Notation "'ND'" := (Injectable ND.Shape ND.Pos Shape Pos).
  Notation "'Trace'" := (Traceable Shape Pos).
  Notation "'Maybe'" := (Injectable Maybe.Shape Maybe.Pos Shape Pos).

  (* Non-deterministic integer. *)
  Definition coin `{ND}
  := @share Shape Pos S _ _ (pure 0%Z) >>= fun c1 =>
     @share Shape Pos S _ _ (pure 1%Z) >>= fun c2 =>
     Choice Shape Pos c1 c2.

  (* Non-deterministic boolean value. *)
  Definition coinB `{ND}
  := @share Shape Pos S _ _ (True_ Shape Pos) >>= fun c1 =>
     @share Shape Pos S _ _ (False_ Shape Pos) >>= fun c2 =>
     Choice Shape Pos c1 c2.

  (* Non-deterministic partial integer. *)
  Definition coinM `{ND} `{Maybe}
  := @share Shape Pos S _ _ (Nothing Shape Pos) >>= fun c1 =>
     @share Shape Pos S _ _ (Just Shape Pos 1%Z) >>= fun c2 =>
     Choice Shape Pos c1 c2.

  (* (0 ? 1, 2 ? 3) *)
  Definition coinPair `{ND}
  : Free Shape Pos (Pair Shape Pos (Integer Shape Pos) (Integer Shape Pos))
  := @share Shape Pos S _ _ (pure 0%Z) >>= fun c1 =>
     @share Shape Pos S _ _ (pure 1%Z) >>= fun c2 =>
     @share Shape Pos S (Integer Shape Pos) _
          (Choice Shape Pos c1 c2) >>= fun c3 =>
     @share Shape Pos S _ _ (pure 2%Z) >>= fun c4 =>
     @share Shape Pos S _ _ (pure 3%Z) >>= fun c5 =>
     @share Shape Pos S (Integer Shape Pos) _
          (Choice Shape Pos c4 c5) >>= fun c6 =>
     Pair_ Shape Pos c3 c6.

  (* [0 ? 1, 2 ? 3] *)
  Definition coinList `{ND}
  : Free Shape Pos (List Shape Pos (Integer Shape Pos))
  := @share Shape Pos S _ _ (pure 0%Z) >>= fun c1 =>
     @share Shape Pos S _ _ (pure 1%Z) >>= fun c2 =>
     @share Shape Pos S _ _ (Choice Shape Pos c1 c2) >>= fun c3 =>
     @share Shape Pos S _ _ (pure 2%Z) >>= fun c4 =>
     @share Shape Pos S _ _ (pure 3%Z) >>= fun c5 =>
     @share Shape Pos S _ _ (Choice Shape Pos c4 c5) >>= fun c6 =>
     @share Shape Pos S _ _ (Nil Shape Pos) >>= fun c7 =>
     @share Shape Pos S _ _ (Cons Shape Pos c6 c7) >>= fun c8 =>
     Cons Shape Pos c3 c8.

  (* Traced integer. *)
  Definition traceOne `{Trace}
  := @share Shape Pos S _ _ (pure 1%Z) >>= fun c1 =>
     trace "One" c1.

  (* Traced boolean values. *)
  Definition traceTrue `{Trace}
  := @share Shape Pos S _ _ (True_ Shape Pos) >>= fun c1 =>
     trace "True" c1.

  Definition traceFalse `{Trace}
  := @share Shape Pos S _ _ (False_ Shape Pos) >>= fun c1 =>
     trace "False" c1.

  (* Traced Maybe values *)
  Definition traceNothing `{Trace} `{M : Maybe}
  := @share Shape Pos S _ _ (@Nothing Shape Pos M (Integer Shape Pos)) >>= fun c1 =>
     trace "Nothing" c1.

  Definition traceJust `{Trace} `{M : Maybe}
  := @share Shape Pos S _ _ (@Just Shape Pos M _ 1%Z) >>= fun c1 =>
     trace "Just 1" c1.

  (* (trace "0" 0, trace "1" 1) *)
  Definition tracePair `{Trace}
  : Free Shape Pos (Pair Shape Pos (Integer Shape Pos) (Integer Shape Pos))
  := @share Shape Pos S _ _ (pure 0%Z) >>= fun c1 =>
     @share Shape Pos S _ _ (pure 1%Z) >>= fun c2 =>
     @share Shape Pos S _ _ (trace "0" c1) >>= fun c3 =>
     @share Shape Pos S _ _ (trace "1" c2) >>= fun c4 =>
     Pair_ Shape Pos c3 c4.

  (* [trace "0" 0, trace "1" 1] *)
  Definition traceList `{Trace}
  : Free Shape Pos (List Shape Pos (Integer Shape Pos))
  := @share Shape Pos S _ _ (pure 0%Z) >>= fun c1 =>
     @share Shape Pos S _ _ (trace "0" c1) >>= fun c2 =>
     @share Shape Pos S _ _ (pure 1%Z) >>= fun c3 =>
     @share Shape Pos S _ _ (trace "1" c3) >>= fun c4 =>
     @share Shape Pos S _ _ (Nil Shape Pos) >>= fun c5 =>
     @share Shape Pos S _ _ (Cons Shape Pos c4 c5) >>= fun c6 =>
     (Cons Shape Pos c2 c6).

  (* [trace "1" 1, trace "2" 2, trace "3" 3] *)
  Definition traceList3 `{Trace}
  : Free Shape Pos (List Shape Pos (Integer Shape Pos))
  := @share Shape Pos S _ _ (pure 1%Z) >>= fun c1 =>
     @share Shape Pos S _ _ (trace "1" c1) >>= fun c2 =>
     @share Shape Pos S _ _ (pure 2%Z) >>= fun c3 =>
     @share Shape Pos S _ _ (trace "2" c3) >>= fun c4 =>
     @share Shape Pos S _ _ (pure 3%Z) >>= fun c5 =>
     @share Shape Pos S _ _ (trace "3" c5) >>= fun c6 =>
     @share Shape Pos S _ _ (Nil Shape Pos) >>= fun c7 =>
     @share Shape Pos S _ _ (Cons Shape Pos c6 c7) >>= fun c8 =>
     @share Shape Pos S _ _ (Cons Shape Pos c4 c8) >>= fun c9 =>
     (Cons Shape Pos c2 c9).



End SecData.

(* Arguments sentences for the data. *)
Arguments coin {_} {_} _ {_}.
Arguments coinB {_} {_} _ {_}.
Arguments coinM {_} {_} _ {_} {_}.
Arguments coinPair {_} {_} _ {_}.
Arguments coinList {_} {_} _ {_}.
Arguments traceOne {_} {_} _.
Arguments traceTrue {_} {_} _.
Arguments traceFalse {_} {_} _.
Arguments traceNothing {_} {_} _ {_}.
Arguments traceJust {_} {_} _ {_}.
Arguments tracePair {_} {_} _.
Arguments traceList {_} {_} _.
Arguments traceOne {_} {_} _ {_}.
Arguments traceTrue {_} {_} _ {_}.
Arguments traceFalse {_} {_} _ {_}.
Arguments traceNothing {_} {_} _ {_} {_}.
Arguments traceJust {_} {_} _ {_} {_}.
Arguments tracePair {_} {_} _ {_}.
Arguments traceList {_} {_} _ {_}.
Arguments traceList3 {_} {_} _ {_}.
(* Test functions *)

Section SecFunctions.

  (*Set Implicit Arguments.*)
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Variable S : Strategy Shape Pos.
  Variable A : Type.
  Context `{ShareableArgs Shape Pos A}.

  Notation "'FreeA'" := (Free Shape Pos A).
  Notation "'Maybe'" := (Injectable Maybe.Shape Maybe.Pos Shape Pos).

  (* Simple sharing:
     let sx = fx in f sx sx *)
  Definition doubleShared (f : FreeA -> FreeA -> FreeA) (fx : FreeA)
   : FreeA
  := @share Shape Pos S A _ fx >>= fun sx => f sx sx.

  (* Nested sharing:
     let sx = fx
         sy = f sx sx
     in f sy sy *)
  Definition doubleSharedNested (f : FreeA -> FreeA -> FreeA) (fx : FreeA)
   : FreeA
  := @share Shape Pos S A _ fx >>= fun sx =>
     @share Shape Pos S A _ (f sx sx) >>= fun sy =>
    f sy sy.

  (* let sx = fx
         sy = f sx sx
         sz = fy
    in f sy sz *)
  Definition doubleSharedClash (f : FreeA -> FreeA -> FreeA) (fx : FreeA) (fy : FreeA)
  : FreeA
  := @share Shape Pos S A _ fx >>= fun sx =>
     @share Shape Pos S A _ (f sx sx) >>= fun sy =>
     @share Shape Pos S A _ fy >>= fun sz =>
     f sy sz.

  (*
  let sx = val
     sy = f sx fx
     sz = f sy fy
     c1 = f sz val
     c2 = f sy c1
  in f sx c2
  *)
  Definition doubleSharedRec (f : FreeA -> FreeA -> FreeA)
                             (fx : FreeA) (fy : FreeA)
                             (val : A)
   : FreeA
  := @share Shape Pos S A _ (pure val) >>= fun sx =>
     @share Shape Pos S A _ (f sx fx) >>= fun sy =>
     @share Shape Pos S A _ (f sy fy) >>= fun sz =>
     @share Shape Pos S A _ (f sz sx) >>= fun c1 =>
     @share Shape Pos S A _ (f sy c1) >>= fun c2 =>
     f sx c2.

  (* Deep sharing. *)

  (*
  let sx = fx
      c1 = fst sx
      c2 = fst sx
      in c1 + c2
  *)
  Definition doubleDeepSharedPair (f : FreeA -> FreeA -> FreeA)
                                  (fx : Free Shape Pos (Pair Shape Pos A A))
   : FreeA
  := @share Shape Pos S (Pair Shape Pos A A) _ fx >>= fun sx =>
     @share Shape Pos S A _ (Tuple.fst Shape Pos sx) >>= fun c1 =>
     @share Shape Pos S A _ (Tuple.fst Shape Pos sx) >>= fun c2 =>
      f c1 c2.

  (*
  let sx = fl in head sx + head sx
  Flattened version:
  let sx = fl
      c1 = head sx
      c2 = head sx
  in c1 + c2
  *)
  Definition doubleDeepSharedList (P : Partial Shape Pos)
                                  (f : FreeA -> FreeA -> FreeA)
                                  (fl : Free Shape Pos (List Shape Pos A))
   : FreeA
  := @share Shape Pos S (List Shape Pos A) _ fl >>= fun sx =>
     @share Shape Pos S A _ (List.head Shape Pos P sx) >>= fun c1 =>
     @share Shape Pos S A _ (List.head Shape Pos P sx) >>= fun c2 =>
              f c1 c2.

(* Recursive functions *)


  (*
   tails :: [a] -> [[a]]
   tails xs = xs : case xs of
   []      -> []
   x : xs' -> tails xs'
  *)
  (* fxs' can not be shared because the termination checker does not accept that definition
     as well-formed. But since xs0 is shared (in tails), its component fxs' is also automatically shared. *)
  Fixpoint tails_0 (xs0 : List Shape Pos A) {struct xs0}
   : Free Shape Pos (List Shape Pos (List Shape Pos A))
    := match xs0 with
       | List.nil          =>  Nil Shape Pos
       | List.cons _ fxs' =>  @share Shape Pos S _ _ (fxs' >>= fun xs'0 => tails_0 xs'0) >>= fun c1 =>
                              Cons Shape Pos fxs' c1
       end.

  Definition tails (fxs : Free Shape Pos (List Shape Pos A))
    : Free Shape Pos (List Shape Pos (List Shape Pos A))
   := @share Shape Pos S _ _ fxs >>= fun fxs0 =>
      @share Shape Pos S _ _ (fxs0 >>= fun xs0 => tails_0 xs0) >>= fun c1 =>
        Cons Shape Pos fxs0 c1.

End SecFunctions.

Arguments doubleShared {_} {_} _ {_} {_}.
Arguments doubleSharedClash {_} {_} _ {_} {_}.
Arguments doubleSharedNested {_} {_} _ {_} {_}.
Arguments doubleSharedRec {_} {_} _ {_} {_}.
Arguments doubleDeepSharedPair {_} {_} _ {_} {_}.
Arguments doubleDeepSharedList {_} {_} _ {_} {_}.
Arguments tails {_} {_} _ {_} {_}.

(* Some notations for convenience.
   Since we only provide the sharing instance and functions when the handlers
   are called, the arguments Shape and Pos can be inferred. *)
Notation "'addInteger_'" := (addInteger _ _).
Notation "'orBool_'" := (orBool _ _).

(* ---------------------- Test cases without sharing ----------------------- *)


(*
0?1 + 0?1
= 0+0 ? 0+1 ? 1+0 ? 1+1
= 0 ? 1 ? 1 ? 2
*)
Example exAddNoSharingND : @handle _ _ _ (HandlerShareND _) (doubleShared Cbn addInteger_ (coin Cbn))
                           = [0%Z;1%Z;1%Z;2%Z].
Proof. constructor. Qed.

(*
trace "One" 1 + trace "One" 1
=> The message should be logged twice and the result should be 2.
*)
Example exAddNoSharingTrace
: @handle _ _ _ (HandlerShareTrace _) (doubleShared Cbn addInteger_ (traceOne Cbn))
  = (2%Z,["One";"One"]).
Proof. constructor. Qed.

(*
(true ? false) or (true ? false)
= (true or (true ? false)) ? (false or (true ? false))
= true ? (true ? false)
= true ? true ? false
*)
Example exOrNDNoSharing
 : @handle _ _ _ (HandlerShareND _) (doubleShared Cbn orBool_ (coinB Cbn)) = [true;true;false].
Proof. constructor. Qed.

(*
(trace "True" true) or (trace "True" true)
=> The second argument is not evaluated, so the result should be true and the
   message should be logged only once.
*)
Example exOrTrueTracingNoSharing
 : @handle _ _ _ (HandlerShareTrace _) (doubleShared Cbn orBool_ (traceTrue Cbn))
   = (true,["True"]).
Proof. constructor. Qed.

(*
(trace "False" false) or (trace "False" false)
=> Both arguments are evaluated, so the result should be false and the message
   should be logged twice.
*)
Example exOrFalseTracingNoSharing
 : @handle _ _ _ (HandlerShareTrace _) (doubleShared Cbn orBool_ (traceFalse Cbn))
   = (false,["False";"False"]).
Proof. constructor. Qed.

(*
(trace "False" false) or (trace "True" false)
=> Both arguments are evaluated, so the result should be true and both messages
   should be logged.
*)
Example exOrMixedTracingNoSharing
 : @handle _ _ _ (HandlerShareTrace _) (orBool_ (traceFalse Cbn) (traceTrue Cbn))
   = (true,["False";"True"]).
Proof. constructor. Qed.

(*
(Nothing ? Just 1) + (Nothing ? Just 1)
= Nothing
*)
Example exNDMNoSharing
 : @handle _ _ _ (HandlerShareNDMaybe _) (doubleShared Cbn addInteger_ (coinM Cbn)) = None.
Proof. constructor. Qed.

(*
trace "Nothing" Nothing + trace "Nothing" Nothing
=> The second argument is not evaluated due to >>=, so the message should
   only be logged once and the result should be Nothing (i.e. None in Coq).
*)
Example exTraceNothingNoSharing
 : @handle _ _ _ (HandlerMaybeShareTrace _) (doubleShared Cbn addInteger_ (traceNothing Cbn))
   = (None,["Nothing"]).
Proof. constructor. Qed.

(*
trace "Just 1" (Just 1) + trace "Just 1" (Just 1)
=> Since there is no sharing, the message should be logged twice and the
   result should be Just 2 (Some 2 in Coq).
*)
Example exTraceJustNoSharing
 : @handle _ _ _ (HandlerMaybeShareTrace _) (doubleShared Cbn addInteger_ (traceJust Cbn))
   = (Some 2%Z,["Just 1";"Just 1"]).
Proof. constructor. Qed.


(* --------------------- Test cases for simple sharing --------------------- *)

(*
let sx = 0 ? 1
in sx + sx
= 0+0 ? 1+1
= 0 ? 2
*)
Example exAddSharingND : @handle _ _ _ (HandlerShareND _) (doubleShared Cbneed
  addInteger_ (coin Cbneed))
  = [0%Z;2%Z].
Proof. constructor. Qed.

(* Strict evaluation also leads to consistent choices. *)
Example exAddSharingNDStrict : @handle _ _ _ (HandlerShareND _) (doubleShared Cbv
  addInteger_ (coin Cbv))
  = [0%Z;2%Z].
Proof. constructor. Qed.

(*
let sx = trace "One" 1
in sx + sx
=> The message should be logged once and the result should be 2.
*)
Example exAddSharingTrace
 : @handle _ _ _ (HandlerShareTrace _) (doubleShared Cbneed addInteger_ (traceOne Cbneed))
 = (2%Z,["One"]).
Proof. constructor. Qed.

(* Strict evaluation also leads to the message being logged only once. *)
Example exAddSharingTraceStrict
 : @handle _ _ _ (HandlerShareTrace _) (doubleShared Cbv addInteger_ (traceOne Cbv))
 = (2%Z,["One"]).
Proof. constructor. Qed.

(*
let sx = true ? false
in sx or sx
= (true or true) ? (false or false)
= true ? false
*)
Example exOrNDSharing
 : @handle _ _ _ (HandlerShareND _) (doubleShared Cbneed orBool_ (coinB Cbneed)) = [true;false].
Proof. constructor. Qed.

(* Strict evaluation also leads to consistent choices. *)
Example exOrNDSharingStrict
 : @handle _ _ _ (HandlerShareND _) (doubleShared Cbv orBool_ (coinB Cbv)) = [true;false].
Proof. constructor. Qed.

(*
let sx = trace "True" true
in sx or sx
=> The second argument is not evaluated, so sharing makes no difference here.
   The message should be logged once and the result should be true.
*)
Example exOrTrueTraceSharing
 : @handle _ _ _ (HandlerShareTrace _) (doubleShared Cbneed orBool_ (traceTrue Cbneed))
   = (true,["True"]).
Proof. constructor. Qed.

(* Strict evaluation also leads to the message being logged only once. *)
Example exOrTrueTraceSharingStrict
 : @handle _ _ _ (HandlerShareTrace _) (doubleShared Cbv orBool_ (traceTrue Cbv))
   = (true,["True"]).
Proof. constructor. Qed.

(*
let sx = trace "False" true
in sx or sx
=> Both arguments are evaluated, but sx is shared, so the message should
only be logged once and the result should be false.
*)
Example exOrFalseTraceSharing
 : @handle _ _ _ (HandlerShareTrace _) (doubleShared Cbneed orBool_ (traceFalse Cbneed))
   = (false,["False"]).
Proof. constructor. Qed.

(*
let sx = Nothing ? Just 1
in sx + sx
= Nothing
*)
Example exNDMSharing
 : @handle _ _ _ (HandlerShareNDMaybe _) (doubleShared Cbneed addInteger_ (coinM Cbneed))
   = None.
Proof. constructor. Qed.

(*
let sx = trace "Nothing" Nothing
in sx + sx
=> The message should only be logged once and the result should be Nothing
   due to >>=.
*)
Example exTraceNothingSharing
 : @handle _ _ _ (HandlerMaybeShareTrace _) (doubleShared Cbneed addInteger_ (traceNothing Cbneed))
   = (None,["Nothing"]).
Proof. constructor. Qed.

(*
let sx = trace "Just 1" (Just 1)
in sx + sx
=> The message should only be logged once due to sharing and the result
   should be Some 2.
*)
Example exTraceJustSharing
 : @handle _ _ _ (HandlerMaybeShareTrace _) (doubleShared Cbneed addInteger_ (traceJust Cbneed))
   = (Some 2%Z,["Just 1"]).
Proof. constructor. Qed.

(* --------------------- Test cases for nested sharing --------------------- *)

(*
let sx = 0 ? 1
    sy = sx + sx
in sy + sy
= (0+0)+(0+0) ? (1+1)+(1+1)
= 0 ? 4
*)
Example exAddNestedSharingND : @handle _ _ _ (HandlerShareND _) (doubleSharedNested Cbneed
                                                          addInteger_
                                                          (coin Cbneed))
                               = [0%Z;4%Z].
Proof. constructor. Qed.

(*
let sx = trace "One" 1
    sy = sx + sx
in sy + sy
=> The message should only be logged once and the result should be 4.
*)
Example exAddNestedSharingTrace
 : @handle _ _ _ (HandlerShareTrace _) (doubleSharedNested Cbneed addInteger_ (traceOne Cbneed))
   = (4%Z,["One"]).
Proof. constructor. Qed.

(*
let sx = true ? false
    sy = sx or sx
in sy or sy
= true ? false
*)
Example exOrNestedSharingND
 : @handle _ _ _ (HandlerShareND _) (doubleSharedNested Cbneed orBool_ (coinB Cbneed))
   = [true;false].
Proof. constructor. Qed.

(*
let sx = trace "True" true
    sy = sx or sx
in sy or sy
=> The message should only be logged once due to non-strictness
   and the result should be true.
*)
Example exOrNestedTrueTracing
 : @handle _ _ _ (HandlerShareTrace _) (doubleSharedNested Cbneed orBool_ (traceTrue Cbneed))
   = (true,["True"]).
Proof. constructor. Qed.

(*
let sx = trace "True" true
    sy = sx or sx
in sy or sy
=> The message should only be logged once due to sharing
   and the result should be false.
*)
Example exOrNestedFalseTracing
 : @handle _ _ _ (HandlerShareTrace _) (doubleSharedNested Cbneed orBool_ (traceFalse Cbneed))
   = (false, ["False"]).
Proof. constructor. Qed.

(*
let sx = 0 ? 1
    sy = sx + sx
    sz = 0 ? 1
in sy + sz
= ((0 + 0) ? (1 + 1)) + (0 ? 1)
= (0 ? 1) + (0 ? 1)
= 0+0 ? 0+1 ? 1+0 ? 1+1
= 0 ? 1 ? 2 ? 3
*)
Example exAddClashSharingND
 : @handle _ _ _ (HandlerShareND _) (doubleSharedClash Cbneed addInteger_ (coin Cbneed) (coin Cbneed))
   = [0%Z;1%Z;2%Z;3%Z].
Proof. constructor. Qed.

(*
let sx = trace "One" 1
    sy = sx + sx
    sz = trace "One" 1
in sy + sz
=> The message should be logged twice and the result should be 3.
*)
Example exAddClashSharingTracing
 : @handle _ _ _ (HandlerShareTrace _) (doubleSharedClash Cbneed addInteger_
                                  (traceOne Cbneed) (traceOne Cbneed))
   = (3%Z,["One";"One"]).
Proof. constructor. Qed.

(*
let sx = true ? false
    sy = sx or sx
    sz = true ? false
in sy or sz
= ((true or true) or (true ? false)) ? ((false or false) or (true ? false))
= true ? (true ? false)
= true ? true ? false
*)
Example exOrClashSharingND
 : @handle _ _ _ (HandlerShareND _) (doubleSharedClash Cbneed orBool_ (coinB Cbneed) (coinB Cbneed))
   = [true;true;false].
Proof. constructor. Qed.

(*
let sx = trace "True" true
    sy = sx or sx
    sz = trace "True" true
in sy or sz
=> The message should only be logged once due to non-strictness and the
   result should be true.
*)
Example exOrClashTrueTracing
 : @handle _ _ _ (HandlerShareTrace _) (doubleSharedClash Cbneed orBool_
                                  (traceTrue Cbneed) (traceTrue Cbneed))
   = (true,["True"]).
Proof. constructor. Qed.

(*
let sx = trace "False" false
    sy = sx or sx
    sz = trace "False" false
in sy or sz
=> sx is shared, so evaluating sy should only log one message.
   Evaluating sz should log the message once more, so it should
   be logged twice in total and the result should be false.
*)
Example exOrClashFalseTracing
 : @handle _ _ _ (HandlerShareTrace _) (doubleSharedClash Cbneed orBool_
                                  (traceFalse Cbneed) (traceFalse Cbneed))
   = (false,["False";"False"]).
Proof. constructor. Qed.

(*
let sx = 1
    sy = sx + (0 ? 1)
    sz = sy + (0 ? 1)
in sx + (sy + (sz + 1))
= (1 + (1+0 + ((1+0 + (0 ? 1)) + 1))) ? (1 + (1+1 + ((1+1 + (0 ? 1)) + 1)))
= (1 + (1+0 + ((1+0 + 0) + 1)))
  ? (1 + (1+0 + ((1+0 + 1) + 1)))
  ? (1 + (1+1 + ((1+1 + 0) + 1)))
  ? (1 + (1+1 + ((1+1 + 1) + 1)))
= 4 ? 5 ? 6 ? 7
*)
Example exAddRecSharingND : @handle _ _ _ (HandlerShareND _) (doubleSharedRec Cbneed
                                                    addInteger_
                                                    (coin Cbneed) (coin Cbneed) 1%Z)
                            = [4%Z;5%Z;6%Z;7%Z].
Proof. constructor. Qed.

(*
let sx = 1
    sy = sx + trace "One" 1
    sz = sy + trace "One" 1
in sx + (sy + (sz + 1))
=> The message should be logged once for sy and once for sz, so it should be
   logged twice in total.
   sx has the value 1, sy has the value 2 and sz has the value 3, so the
   final value should be 1 + 2 + 3 + 1 = 7.
*)
Example exAddRecSharingTracing
 : @handle _ _ _ (HandlerShareTrace _) (doubleSharedRec Cbneed addInteger_
                                (traceOne Cbneed) (traceOne Cbneed) 1%Z)
   = (7%Z,["One";"One"]).
Proof. constructor. Qed.

(*
let sx = true
    sy = sx or (true ? false)
    sz = sy or (true ? false)
in sx or (sy or (sz or true))
= true (due to non-strictness)
*)
Example exOrRecSharingNDTrue
 : @handle _ _ _ (HandlerShareND _) (doubleSharedRec Cbneed orBool_ (coinB Cbneed) (coinB Cbneed) true)
   = [true].
Proof. constructor. Qed.

(*
let sx = false
    sy = sx or (true ? false)
    sz = sy or (true ? false)
in sx or (sy or (sz or false))
= false or ((false or true) or ((true or (true ? false)) or false)) ?
  false or ((false or false) or ((false or (true ? false)) or false))
= (false or true) or ((true or (true ? false)) or false) ?
  (false or false) or ((false or (true ? false)) or false)
= true ?
  (false or (true ? false)) or false
= true ?
  (true ? false) or false
= true ?
  true or false ?
  false or false
= true ? true ? false
*)
Example exOrRecSharingNDFalse
 : @handle _ _ _ (HandlerShareND _) ((doubleSharedRec Cbneed orBool_ (coinB Cbneed) (coinB Cbneed) false))
   = [true;true;false].
Proof. constructor. Qed.

(*
let sx = false
    sy = sx or (trace "True" true)
    sz = sy or (trace "True" true)
in sx or (sy or (sz or false))
=> sy has the value true, so sz is not evaluated. The message should only
   be logged once and the result should be true.
*)
Example exOrRecTrueTracing
 : @handle _ _ _ (HandlerShareTrace _) (doubleSharedRec Cbneed orBool_
                                (traceTrue Cbneed) (traceTrue Cbneed) false)
   = (true,["True"]).
Proof. constructor. Qed.

(*
let sx = false
    sy = sx or (trace "False" false)
    sz = sy or (trace "False" false)
in sx or (sy or (sz or false))
=> sy is shared, so its message should only be logged once. Additionally,
   the message is logged once more when sz is evaluated. The result should
   be false.
*)
Example exOrRecFalseTracing
 : @handle _ _ _ (HandlerShareTrace _) (doubleSharedRec Cbneed orBool_
                                (traceFalse Cbneed) (traceFalse Cbneed) false)
   = (false,["False";"False"]).
Proof. constructor. Qed.


(* ----------------------- Test cases for deep sharing --------------------- *)

(*
let sx = (0 ? 1, 2 ? 3)
in fst sx + fst sx

= (0 + 0) ? (1 + 1)
= 0 ? 2
*)
Example exAddDeepPairND
 : @handle _ _ _ (HandlerShareND _) (doubleDeepSharedPair Cbneed addInteger_ (coinPair Cbneed))
  = [0%Z;2%Z].
Proof. constructor. Qed.

(* let sx = [0 ? 1, 2 ? 3]
in head sx + head sx
= (0 + 0) ? (1 + 1)
= 0 ? 2
*)
Example exAddDeepListND
 : @handle _ _ _ (HandlerShareND _)
  (doubleDeepSharedList Cbneed (ND.Partial _ _) addInteger_ (coinList Cbneed))
 = [0%Z;2%Z].
Proof. constructor. Qed.

(*
let sx = (trace "0" 0, trace "1" 1)
in fst sx + fst sx
=> The pair is shared, so the effects inside the pair should be shared as
   well. Since we take the first element twice, the second tracing message ("1")
   should not be logged and the first should be shared and thus logged once.
*)
Example exAddDeepPairTrace
 : @handle _ _ _ (HandlerShareTrace _) (doubleDeepSharedPair Cbneed addInteger_ (tracePair Cbneed))
  = (0%Z, ["0"]).
Proof. constructor. Qed.

(*
let sx = (trace "0" 0, trace "1" 1)
in head sx + head sx
=> The list is shared, so the effects inside the pair should be shared as
   well. Since we take the first element twice, the second tracing message ("1")
   should not be logged and the first should be shared and thus logged once.
   Because head is partial and we use the Maybe instance of Partial, the result
   should be Some 0 instead of simply 0.
*)
Example exAddDeepListTrace
 : @handle _ _ _ (HandlerMaybeShareTrace _)
   (doubleDeepSharedList Cbneed (Maybe.Partial _ _)
      addInteger_ (traceList Cbneed))
  = (Some 0%Z, ["0"]).
Proof. constructor. Qed.

(*
  sumTails :: [Integer] -> Integer
  sumTails l = sum (map sum (tails l))
*)
Definition sumTails
  (Shape : Type) (Pos : Shape -> Type)
  (S : Strategy Shape Pos)
  (l : Free Shape Pos (List Shape Pos (Integer Shape Pos)))
  : Free Shape Pos (Integer Shape Pos)
 := List.sum Shape Pos S >>= fun f => f
      (List.map Shape Pos S (pure (fun fxs => List.sum Shape Pos S >>= (fun g => g fxs)))
                            (tails S l)).

(* Evaluation of sumTails [trace "1" 1, trace "2" 2, trace "3" 3] *)
(* = sum (map (sum [trace "1" 1, trace "2" 2, trace "3" 3] : [trace "2" 2, trace "3" 3] : [trace "3" 3] : [])) *)

(* Call-by-need *)
(* Due to sharing, each number should be logged only once. *)
Example exSumTailsTracingCbneed : @handle _ _ _ (HandlerShareTrace _) (sumTails _ _ Cbneed (traceList3 Cbneed))
 = (14%Z,["1";"2";"3"]).
Proof. constructor. Qed.

(* Call-by-name *)
(* Each time an element is evaluated, its message is logged again.
   Only one of the lists in the result of tails contains 1, two contain 2,
   and three contain 3. Therefore, "1" should be logged once, "2" twice and
   "3" three times. *)
Example exSumTailsTracingCbn : @handle _ _ _ (HandlerShareTrace _) (sumTails _ _ Cbn (traceList3 Cbn))
 = (14%Z,["1";"2";"3";"2";"3";"3"]).
Proof. constructor. Qed.

(* Call-by-value *)
(* The tracing effect is evaluated immediately, so we should only log each number once. *)
Example exSumTailsTracingCbv : @handle _ _ _ (HandlerShareTrace _) (sumTails _ _ Cbv (traceList3 Cbv))
 = (14%Z,["1";"2";"3"]).
Proof. constructor. Qed.

(* Evaluation of sumTails [0 ? 1, 2 ? 3] *)

(* Call-by-need *)
(* sumTails [0 ? 1, 2 ? 3]
  = sum (map sum (tails [0 ? 1, 2 ? 3]))
  = sum (map sum ( [0 ? 1, 2 ? 3] : tails [ 2 ? 3 ]  ))
  = sum (map sum ( [0 ? 1, 2 ? 3] : ([2 ? 3] : [])  ))
  = sum (map sum ([[0,2],[2]] ? [[0,3], [3]] ? [[1,2],[2]] ? [[1,3],[3]] ))
  = sum ([2,2] ? [3,3] ? [3,2] ? [4,3])
  = 4 ? 6 ? 5 ? 7
*)
Example exSumTailsNDCbneed : @handle _ _ _ (HandlerShareND _) (sumTails _ _ Cbneed (coinList Cbneed))
 = [4%Z;6%Z;5%Z;7%Z].
Proof. constructor. Qed.

(* Call-by-name *)
(*
  sumTails [0 ? 1, 2 ? 3]
  = sum (map sum (tails [0 ? 1, 2 ? 3]))
  = sum (map sum ( [0 ? 1, 2 ? 3] : tails [ 2 ? 3 ]  ))
  = sum (map sum ( [0 ? 1, 2 ? 3] : ([2 ? 3] : [])  ))
  = sum ([2,2] ? [3,2] ? [2,3] ? [3,3] ? [3,2] ? [3,3] ? [4,2] ? [4,3])
  = 4 ? 5 ? 5 ? 6 ? 5 ? 6 ? 6 ? 7
*)
Example exSumTailsNDCbn : @handle _ _ _ (HandlerShareND _) (sumTails _ _ Cbn (coinList Cbn))
 = [4%Z;5%Z;5%Z;6%Z;5%Z;6%Z;6%Z;7%Z].
Proof. constructor. Qed.

(* Call-by-value *)
(* Because the non-determinism is evaluated immediately, the result should be
   the same as with call-by-need evaluation. *)
Example exSumTailsNDCbv : @handle _ _ _ (HandlerShareND _) (sumTails _ _ Cbv (coinList Cbv))
 = [4%Z;6%Z;5%Z;7%Z].
Proof. constructor. Qed.
