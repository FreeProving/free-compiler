(** * Test module for sharing handlers. *)

From Base Require Import Free.
From Base Require Import Free.Instance.Comb.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Instance.Maybe.
From Base Require Import Free.Instance.ND.
From Base Require Import Free.Instance.Share.
From Base Require Import Free.Instance.Trace.

From Base Require Import Free.Malias.

From Base Require Import Prelude.Bool.
From Base Require Import Prelude.Integer.

From Base Require Import Free.Util.Search.

Require Import Lists.List.
Import List.ListNotations.


(* TODO: Put ShareableArgs in Class *)
From Base Require Import Free.Class.ShareableArgs.

(* Shortcut to evaluate a non-deterministic program to a result list.
   list. *)
Definition evalND {A : Type} p
:= @collectVals A (run (runChoice (runNDSharing (0,0) p))).

(* Shortcut to evaluate a traced program to a result and a list of logged 
   messages. *)
Definition evalTracing {A : Type} p 
:= @collectMessages A (run (runTracing (runTraceSharing (0,0) p))).

(* Shortcut to evaluate a non-deterministic partial program to a result 
   list. *)
Definition evalNDM {A : Type} p
:= @collectVals (option A) (run (runChoice (runNDSharing (0,0) (runMaybe p)))).

(* Shortcut to evaluate a traced partial program to a result and a list 
   of logged messages. *)
Definition evalTraceM {A : Type} p
:= @collectMessages (option A) 
   (run (runTracing (runTraceSharing (0,0) (runMaybe p)))).

(* Non-deterministic integer. *)
Definition coin (Shape : Type) (Pos : Shape -> Type)
                `{Injectable ND.Shape ND.Pos Shape Pos}
 : Free Shape Pos (Integer Shape Pos)
:= Choice Shape Pos (pure 0%Z) (pure 1%Z).
Arguments coin {_} {_} {_}.


(* Non-deterministic boolean value. *)
Definition coinB (Shape : Type) (Pos : Shape -> Type)
                 `{Injectable ND.Shape ND.Pos Shape Pos}
 := Choice Shape Pos (True_ _ _) (False_ _ _).
Arguments coinB {_} {_} {_}.

(* Non-deterministic partial integer. *)
Definition coinM (Shape : Type) (Pos : Shape -> Type)
                 `{Injectable ND.Shape ND.Pos Shape Pos}
                 `{Injectable Maybe.Shape Maybe.Pos Shape Pos}
:= Choice Shape Pos (Nothing_inj _ _) (Just_inj _ _ 1%Z).
Arguments coinM {_} {_} {_} {_}.

(* Traced integer. *)
Definition traceOne (Shape : Type) (Pos : Shape -> Type)
                    `{Traceable Shape Pos}
:= trace "One" (pure 1%Z).
Arguments traceOne {_} {_} {_}.

(* Traced boolean values. *)
Definition traceTrue (Shape : Type) (Pos : Shape -> Type)
                     `{Traceable Shape Pos}
:= trace "True" (True_ _ _).
Arguments traceTrue {_} {_} {_}.
Definition traceFalse (Shape : Type) (Pos : Shape -> Type)
                      `{Traceable Shape Pos}
:= trace "False" (False_ _ _).
Arguments traceFalse {_} {_} {_}.

(* Traced Maybe values *)
Definition traceNothing (Shape : Type) (Pos : Shape -> Type)
                        `{Traceable Shape Pos}
                        `{Injectable Maybe.Shape Maybe.Pos Shape Pos}
:= trace "Nothing" (@Nothing_inj (Integer Shape Pos) _ _ _).
Arguments traceNothing {_} {_} {_} {_}.
Definition traceJust (Shape : Type) (Pos : Shape -> Type)
                     `{Traceable Shape Pos}
                     `{Injectable Maybe.Shape Maybe.Pos Shape Pos}
:= trace "Just 1" (Just_inj _ _ 1%Z).
Arguments traceJust {_} {_} {_} {_}.

(* Some notations for convenience.
   Since we only provide the sharing instance and functions when the handlers
   are called, the arguments Shape and Pos can be inferred. *)
Notation "'Cbneed_'" := (Cbneed _ _).
Notation "'addInteger_'" := (addInteger _ _).
Notation "'orBool_'" := (orBool _ _).


(* ---------------------- Test cases without sharing ----------------------- *)

(* This function applies the given binary function to the given argument
   twice and does not share the argument. *)
Definition double {Shape : Type}
                  {Pos : Shape -> Type}
                  {A : Type}
                  (f : Free Shape Pos A ->
                       Free Shape Pos A -> 
                       Free Shape Pos A)
                  (fx : Free Shape Pos A)
 : Free Shape Pos A
:= f fx fx.

(* 
0?1 + 0?1
= 0+0 ? 0+1 ? 1+0 ? 1+1
= 0 ? 1 ? 1 ? 2
*)
Example exAddNoSharingND : evalND (double (addInteger_) coin) 
                           = [0%Z;1%Z;1%Z;2%Z].
Proof. constructor. Qed.

(*
trace "One" 1 + trace "One" 1
=> The message should be logged twice and the result should be 2.
*)
Example exAddNoSharingTrace 
: evalTracing (double (addInteger_) traceOne) 
  = (2%Z,["One"%string;"One"%string]).
Proof. constructor. Qed.

(*
(true ? false) or (true ? false)
= (true or (true ? false)) ? (false or (true ? false))
= true ? (true ? false)
= true ? true ? false
*)
Example exOrNDNoSharing 
 : evalND (double (orBool_) coinB) = [true;true;false].
Proof. constructor. Qed.

(*
(trace "True" true) or (trace "True" true)
=> The second argument is not evaluated, so the result should be true and the 
   message should be logged only once.
*)
Example exOrTrueTracingNoSharing 
 : evalTracing (double (orBool_) traceTrue) 
   = (true,["True"%string]).
Proof. constructor. Qed.

(*
(trace "False" false) or (trace "False" false)
=> Both arguments are evaluated, so the result should be false and the message
   should be logged twice.
*)
Example exOrFalseTracingNoSharing 
 : evalTracing (double (orBool_) traceFalse) 
   = (false,["False"%string;"False"%string]).
Proof. constructor. Qed.

(*
(trace "False" false) or (trace "True" false)
=> Both arguments are evaluated, so the result should be true and both messages
   should be logged.
*)
Example exOrMixedTracingNoSharing
 : evalTracing (orBool_ traceFalse traceTrue) 
   = (true,["False"%string;"True"%string]).
Proof. constructor. Qed.

(*
(Nothing ? Just 1) + (Nothing ? Just 1)
= (Nothing + (Nothing ? Just 1)) ? (Just 1 + (Nothing ? Just 1))
= Nothing ? (Just 1 + (Nothing ? Just 1))
= Nothing ? (Just 1 + Nothing ? Just 1 + Just 1)
= Nothing ? Nothing ? Just 2
*)
Example exNDMNoSharing
 : evalNDM (double (addInteger_) coinM) = [None;None;Some 2%Z].
Proof. constructor. Qed.

(* 
trace "Nothing" Nothing + trace "Nothing" Nothing
=> The second argument is not evaluated due to >>=, so the message should
   only be logged once and the result should be Nothing (i.e. None in Coq).
*)
Example exTraceNothingNoSharing
 : evalTraceM (double (addInteger_) traceNothing) 
   = (None,["Nothing"%string]).
Proof. constructor. Qed.

(*
trace "Just 1" (Just 1) + trace "Just 1" (Just 1)
=> Since there is no sharing, the message should be logged twice and the 
   result should be Just 2 (Some 2 in Coq).
*)
Example exTraceJustNoSharing
 : evalTraceM (double (addInteger_) traceJust)
   = (Some 2%Z,["Just 1"%string;"Just 1"%string]).
Proof. constructor. Qed.

(*
Instance ShareableArgsGeneric (Shape : Type) (Pos : Shape -> Type)
                              (A : Type)
 : ShareableArgs Shape Pos A := {
     shareArgs := pure
}.
*)
Instance ShareableArgsInteger (Shape : Type) (Pos : Shape -> Type)
                              `{Injectable Share.Shape Share.Pos Shape Pos}
 : ShareableArgs Shape Pos (Integer Shape Pos) := {
    shareArgs n := pure n
}.

Instance ShareableArgsBool (Shape : Type) (Pos : Shape -> Type)
                           
 : ShareableArgs Shape Pos (Bool Shape Pos) := {
    shareArgs b := pure b
}.

(* --------------------- Test cases for simple sharing --------------------- *)
(* let sx = fx in f sx sx *)
Definition doubleShared {Shape : Type}
                        {Pos : Shape -> Type}
                        {A : Type}
                        (S : Shareable Shape Pos)
                        {SA : ShareableArgs Shape Pos A}
                        (f : Free Shape Pos A ->
                             Free Shape Pos A -> 
                             Free Shape Pos A)
                        (fx : Free Shape Pos A)
 : Free Shape Pos A
:= share fx >>= fun sx => f sx sx.

Definition doubleShared' {Shape : Type}
                        {Pos : Shape -> Type}
                        {A : Type}
                        `{Injectable ND.Shape ND.Pos Shape Pos}
                        (S : Shareable Shape Pos)
                        (SA : ShareableArgs Shape Pos A)
                        (f : Free Shape Pos A ->
                             Free Shape Pos A -> 
                             Free Shape Pos A)
                        (fx : Free Shape Pos A)
 : Free Shape Pos A
:= share fx >>= fun sx => share coin >>= fun sy => f sx sx.


Set Typeclasses Debug.
Compute evalND (cbneed _ _ coin >>= fun sc => addInteger _ _ sc sc).
Compute evalND (doubleShared (Cbneed _ _)
  (addInteger _ _) coin).
Compute evalND (doubleShared (Cbn _ _) 
  (addInteger _ _) coin).
Compute evalND (doubleShared' (Cbneed _ _) _
  (addInteger _ _) coin).

(*
let sx = 0 ? 1 
in sx + sx 
= 0+0 ? 1+1
= 0 ? 2
*)
Example exAddSharingND : evalND (doubleShared Cbneed_
  (addInteger_) coin) 
  = [0%Z;2%Z].
Proof. constructor. Qed.

(*
let sx = trace "One" 1
in sx + sx
=> The message should be logged once and the result should be 2.
*)
Example exAddSharingTrace 
 : evalTracing (doubleShared Cbneed_ (addInteger_) traceOne) 
 = (2%Z,["One"%string]).
Proof. constructor. Qed.

(*
let sx = true ? false
in sx or sx
= (true or true) ? (false or false)
= true ? false
*)
Example exOrNDSharing
 : evalND (doubleShared Cbneed_ (orBool_) coinB) = [true;false].
Proof. constructor. Qed.

(*
let sx = trace "True" true
in sx or sx 
=> The second argument is not evaluated, so sharing makes no difference here.
   The message should be logged once and the result should be true.
*)
Example exOrTrueTraceSharing
 : evalTracing (doubleShared (Cbneed_) (orBool_) traceTrue)
   = (true,["True"%string]).
Proof. constructor. Qed.

(*
let sx = trace "False" true
in sx or sx
=> Both arguments are evaluated, but sx is shared, so the message should
only be logged once and the result should be false.
*)
Example exOrFalseTraceSharing
 : evalTracing (doubleShared (Cbneed_) (orBool_) traceFalse)
   = (false,["False"%string]).
Proof. constructor. Qed.

(* traceFalse is shared, but does not occur more than once. 
   Therefore, sharing should make no difference here. *)
Example exOrMixedTraceSharing
 : evalTracing (share traceFalse >>= fun sx => 
                (orBool_ sx traceTrue))
   = (true,["False"%string;"True"%string]).
Proof. constructor. Qed.

(*
let sx = Nothing ? Just 1
in sx + sx
= Nothing + Nothing ? Just 1 + Just 1
= Nothing ? Just 2
*)
Example exNDMSharing
 : evalNDM (doubleShared (Cbneed_) (addInteger_) coinM)
   = [None;Some 2%Z].
Proof. constructor. Qed.

(*
let sx = trace "Nothing" Nothing
in sx + sx
=> The message should only be logged once and the result should be Nothing
   due to >>=.
*)
Example exTraceNothingSharing
 : evalTraceM (doubleShared (Cbneed_) (addInteger_) traceNothing)
   = (None,["Nothing"%string]).
Proof. constructor. Qed.

(*
let sx = trace "Just 1" (Just 1)
in sx + sx 
=> The message should only be logged once due to sharing and the result 
   should be Some 2.
*)
Example exTraceJustSharing
 : evalTraceM (doubleShared (Cbneed_) (addInteger_) traceJust)
   = (Some 2%Z,["Just 1"%string]).
Proof. constructor. Qed.

(* --------------------- Test cases for nested sharing --------------------- *)

(* let sx = fx 
       sy = f sx sx
   in f sy sy *)
Definition doubleSharedNested {Shape : Type}
                              {Pos : Shape -> Type}
                              {A : Type}
                              (S : Shareable Shape Pos)
                              (f : Free Shape Pos A ->
                                  Free Shape Pos A -> 
                                  Free Shape Pos A)
                                  (fx : Free Shape Pos A)
 : Free Shape Pos A
:= share (share fx >>= fun sx => f sx sx) >>= fun sy =>
   f sy sy.

(* 
let sx = 0 ? 1 
    sy = sx + sx 
in sy + sy 
= (0+0)+(0+0) ? (1+1)+(1+1) 
= 0 ? 4 
*)
Example exAddNestedSharingND : evalND (doubleSharedNested (Cbneed_)
                                                          (addInteger_) 
                                                          coin) 
                               = [0%Z;4%Z].
Proof. constructor. Qed.

(* 
let sx = trace "One" 1
    sy = sx + sx 
in sy + sy 
=> The message should only be logged once and the result should be 4. 
*)
Example exAddNestedSharingTrace 
 : evalTracing (doubleSharedNested (Cbneed_) (addInteger_) traceOne) 
   = (4%Z,["One"%string]).
Proof. constructor. Qed.

(*
let sx = true ? false
    sy = sx or sx
in sy or sy
= true ? false
*)
Example exOrNestedSharingND
 : evalND (doubleSharedNested (Cbneed_) (orBool_) coinB)
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
 : evalTracing (doubleSharedNested (Cbneed_) (orBool_) traceTrue)
   = (true,["True"%string]).
Proof. constructor. Qed.

(*
let sx = trace "True" true
    sy = sx or sx
in sy or sy
=> The message should only be logged once due to sharing
   and the result should be false.
*)
Example exOrNestedFalseTracing
 : evalTracing (doubleSharedNested (Cbneed_) (orBool_) traceFalse)
   = (false, ["False"%string]).
Proof. constructor. Qed.

(* let sx = fx  
       sy = f sx sx
       sz = fy
   in f sy sz *)
Definition doubleSharedClash {Shape : Type}
                             {Pos : Shape -> Type}
                             {A : Type}
                             (S : Shareable Shape Pos)
                             (f : Free Shape Pos A ->
                                  Free Shape Pos A -> 
                                  Free Shape Pos A)
                             (fx : Free Shape Pos A)
                             (fy : Free Shape Pos A)
 : Free Shape Pos A
:= share (share fx >>= fun sx => f sx sx) >>= fun sy =>
   share fy >>=  fun sz => f sy sz.

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
 : evalND (doubleSharedClash (Cbneed_) (addInteger_) coin coin) 
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
 : evalTracing (doubleSharedClash (Cbneed_) (addInteger_)
                                  traceOne traceOne) 
   = (3%Z,["One"%string;"One"%string]).
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
 : evalND (doubleSharedClash (Cbneed_) (orBool_) coinB coinB)
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
 : evalTracing (doubleSharedClash (Cbneed_) (orBool_)
                                  traceTrue traceTrue)
   = (true,["True"%string]).
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
 : evalTracing (doubleSharedClash (Cbneed_) (orBool_)
                                  traceFalse traceFalse)
   = (false,["False"%string;"False"%string]).
Proof. constructor. Qed.

(*
let sx = val
    sy = f sx fx
    sz = f sy fy
in f sx (f (sy (f sz val))) 
*)
Definition doubleSharedRec {Shape : Type}
                           {Pos : Shape -> Type}
                           {A : Type}
                           (S : Shareable Shape Pos)
                           (f : Free Shape Pos A ->
                                Free Shape Pos A -> 
                                Free Shape Pos A)
                           (fx : Free Shape Pos A)
                           (fy : Free Shape Pos A)
                           (val : A)
 : Free Shape Pos A
:= share (pure val) >>= fun sx =>
   f sx (share (f sx fx) >>= fun sy => 
      f sy (share (f sy fy) >>= fun sz =>
        f sz (pure val)
      )
   ).

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
Example exAddRecSharingND : evalND (doubleSharedRec (Cbneed_)
                                                    (addInteger_) 
                                                    coin coin 1%Z) 
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
 : evalTracing (doubleSharedRec (Cbneed_) (addInteger_)
                                traceOne traceOne 1%Z) 
   = (7%Z,["One"%string;"One"%string]).
Proof. constructor. Qed.

(*
let sx = true
    sy = sx or (true ? false)
    sz = sy or (true ? false)
in sx or (sy or (sz or true))
= true (due to non-strictness)
*)
Example exOrRecSharingNDTrue
 : evalND (doubleSharedRec (Cbneed_) (orBool_) coinB coinB true)
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
 : evalND (doubleSharedRec (Cbneed_) (orBool_) coinB coinB false)
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
 : evalTracing (doubleSharedRec (Cbneed_) (orBool_)
                                traceTrue traceTrue false)
   = (true,["True"%string]).
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
 : evalTracing (doubleSharedRec (Cbneed_) (orBool_)
                                traceFalse traceFalse false)
   = (false,["False"%string;"False"%string]).
Proof. constructor. Qed.
  