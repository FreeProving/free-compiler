(** * Test module for sharing handlers. *)

From Base Require Import Free.
From Base Require Import Free.HandlerInstances.
From Base Require Import Free.Instance.Comb.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Instance.Maybe.
From Base Require Import Free.Instance.ND.
From Base Require Import Free.Instance.Share.
From Base Require Import Free.Instance.Trace.

From Base Require Import Free.Malias.
From Base Require Import Free.Util.Search.
From Base Require Import Free.Verification.Util.

From Base Require Import Prelude.

Require Import Lists.List.
Import List.ListNotations.

Section SecData.

  Variable Shape : Type.
  Variable Pos : Shape -> Type.

  Notation "'ND'" := (Injectable ND.Shape ND.Pos Shape Pos).
  Notation "'Trace'" := (Traceable Shape Pos).
  Notation "'Maybe'" := (Injectable Maybe.Shape Maybe.Pos Shape Pos).
  Notation "'Share'" := (Injectable Share.Shape Share.Pos Shape Pos).

  (* Non-deterministic integer. *)
  Definition coin `{ND} `{I : Share} (S : Strategy Shape Pos)
  := Choice Shape Pos (pure 0%Z) (pure 1%Z).

  (* Non-deterministic boolean value. *)
  Definition coinB `{ND} `{I : Share} (S : Strategy Shape Pos)
  := Choice Shape Pos (True_ Shape Pos) (False_ Shape Pos).

  (* Non-deterministic partial integer. *)
  Definition coinM `{ND} `{Maybe} `{I : Share} (S : Strategy Shape Pos)
  := Choice Shape Pos 
      (@call Shape Pos I S _ (@Nothing_inj Shape Pos _ (Integer Shape Pos)) >>= fun c0 => c0)
      (@call Shape Pos I S _ (Just_inj Shape Pos 1%Z) >>= fun c0 => c0).

  (* (0 ? 1, 2 ? 3) *)
  Definition coinPair `{ND} `{I : Share} (S : Strategy Shape Pos)
  : Free Shape Pos (Pair Shape Pos (Integer Shape Pos) (Integer Shape Pos))
  := @call Shape Pos I S (Integer Shape Pos) 
          (Choice Shape Pos (pure 0%Z) (pure 1%Z)) >>= fun c1 =>
     @call Shape Pos I S (Integer Shape Pos) 
          (Choice Shape Pos (pure 2%Z) (pure 3%Z)) >>= fun c2 =>
     Pair_ Shape Pos c1 c2.

  (* [0 ? 1, 2 ? 3] *)
  Definition coinList `{ND} `{I : Share} (S : Strategy Shape Pos)
  : Free Shape Pos (List Shape Pos (Integer Shape Pos))
  := @call Shape Pos I S _ (List.Nil Shape Pos) >>= fun c1 =>
     @call Shape Pos I S _ (Choice Shape Pos (pure 2%Z) (pure 3%Z)) >>= fun c2 =>
     @call Shape Pos I S _ (List.Cons Shape Pos c2 c1) >>= fun c3 => 
     @call Shape Pos I S _ (Choice Shape Pos (pure 0%Z) (pure 1%Z)) >>= fun c4 =>
     List.Cons Shape Pos c4 c3.


  (* Traced integer. *)
  Definition traceOne `{Trace}
  := trace "One" (pure 1%Z).

  (* Traced boolean values. *)
  Definition traceTrue `{Trace}
  := trace "True" (True_ Shape Pos).

  Definition traceFalse `{Trace}
  := trace "False" (False_ Shape Pos).

  (* Traced Maybe values *)
  Definition traceNothing `{Trace} `{M : Maybe}
  := trace "Nothing" (@Nothing_inj Shape Pos M (Integer Shape Pos)).

  Definition traceJust `{Trace} `{M : Maybe}
  := trace "Just 1" (@Just_inj Shape Pos M _ 1%Z).

  (* (trace "0" 0, trace "1" 1) *)
  Definition tracePair `{Trace} `{I : Share} (S : Strategy Shape Pos)
  : Free Shape Pos (Pair Shape Pos (Integer Shape Pos) (Integer Shape Pos))
  := @call Shape Pos I S _ (pure 0%Z) >>= fun c1 =>
     @call Shape Pos I S _ (pure 1%Z) >>= fun c2 =>
     @call Shape Pos I S _ (trace "0" c1) >>= fun c3 =>
     @call Shape Pos I S _ (trace "1" c2) >>= fun c4 =>
     Pair_ Shape Pos c3 c4.

  (* [trace "0" 0, trace "1" 1] *)
  Definition traceList `{Trace} `{I : Share} (S : Strategy Shape Pos)
  : Free Shape Pos (List Shape Pos (Integer Shape Pos))
  := @call Shape Pos I S _ (Nil Shape Pos) >>= fun c1 =>
     @call Shape Pos I S _ (pure 1%Z) >>= fun c2 =>
     @call Shape Pos I S _ (trace "1" c2) >>= fun c3 =>
     @call Shape Pos I S _ (Cons Shape Pos c3 c1) >>= fun c4 =>
     @call Shape Pos I S _ (pure 0%Z) >>= fun c5 =>
     @call Shape Pos I S _ (trace "0" c5) >>= fun c6 =>
     (Cons Shape Pos c6 c4).

End SecData.

(* Arguments sentences for the data. *)
Arguments coin {_} {_} {_} {_} _.
Arguments coinB {_} {_} {_} {_} _.
Arguments coinM {_} {_} {_} {_} {_} _.
Arguments coinPair {_} {_} {_} {_} _.
Arguments coinList {_} {_} {_} {_} _.
Arguments traceOne {_} {_} {_}.
Arguments traceTrue {_} {_} {_}.
Arguments traceFalse {_} {_} {_}.
Arguments traceNothing {_} {_} {_} {_}.
Arguments traceJust {_} {_} {_} {_}.
Arguments tracePair {_} {_} {_} {_} _.
Arguments traceList {_} {_} {_} {_} _.

(* Test functions *)
Section SecFunctions.

  Set Implicit Arguments.
  Variable Shape : Type.
  Variable Pos : Shape -> Type.
  Variable A : Type.
  Notation "'FreeA'" := (Free Shape Pos A).
  Notation "'ShareArgs'" := (ShareableArgs Shape Pos A).
  Notation "'Share'" := (Injectable Share.Shape Share.Pos Shape Pos).
  Notation "'Maybe'" := (Injectable Maybe.Shape Maybe.Pos Shape Pos).

  (* Simple sharing: 
     let sx = fx in f sx sx *)
  Definition doubleShared `{I : Share} `{SA : ShareArgs} (S : Strategy Shape Pos)
                        (f : FreeA -> FreeA -> FreeA)
                        (fx : FreeA)
   : FreeA
  := @share Shape Pos I S A SA fx >>= fun sx => f sx sx.

  (* Nested sharing:
     let sx = fx 
         sy = f sx sx
     in f sy sy *)
  Definition doubleSharedNested `{I : Share} `{SA : ShareArgs} (S : Strategy Shape Pos)
                                (f : FreeA -> FreeA -> FreeA)
                                (fx : FreeA)
   : FreeA
  := @share Shape Pos I S A SA fx >>= fun sx => 
     @share Shape Pos I S A SA (f sx sx) >>= fun sy =>
    f sy sy.

  (* let sx = fx  
         sy = f sx sx
         sz = fy
    in f sy sz *)
  Definition doubleSharedClash `{I : Share} `{SA : ShareArgs} (S : Strategy Shape Pos)
                              (f : FreeA -> FreeA -> FreeA)
                              (fx : FreeA) (fy : FreeA)
  : FreeA
  := @share Shape Pos I S A SA fx >>= fun sx =>
     @call Shape Pos I S A (f sx sx) >>= fun sy =>
     @call Shape Pos I S A fy >>= fun sz => 
     f sy sz.

  (*
  let sx = val
     sy = f sx fx
     sz = f sy fy
     c1 = f sz val
     c2 = f sy c1
  in f sx c2
  *)
  Definition doubleSharedRec `{I : Share} `{SA : ShareArgs} (S : Strategy Shape Pos)
                             (f : FreeA -> FreeA -> FreeA)
                            (fx : FreeA) (fy : FreeA)
                            (val : A)
   : FreeA
  := @call Shape Pos I S A (pure val) >>= fun sx =>
     @share Shape Pos I S A SA (f sx fx) >>= fun sy =>
     @share Shape Pos I S A SA (f sy fy) >>= fun sz =>
     @call Shape Pos I S A (f sz sx) >>= fun c1 =>
     @call Shape Pos I S A (f sy c1) >>= fun c2 =>
     f sx c2.

  (* Deep sharing. *)

  (* 
  let sx = fx
      c1 = fst sx
      c2 = fst sx
      in c1 + c2
  *)
  Definition doubleDeepSharedPair `{I : Share} `{SA : ShareArgs} (S : Strategy Shape Pos)
                        (f : FreeA -> FreeA -> FreeA)
                        (fx : Free Shape Pos (Pair Shape Pos A A))
   : FreeA
  := @share Shape Pos I S (Pair Shape Pos A A) _ fx >>= fun sx => 
     @call Shape Pos I S A (fstPair Shape Pos sx) >>= fun c1 =>
     @call Shape Pos I S A (fstPair Shape Pos sx) >>= fun c2 =>
      f c1 c2.

  (* 
  let sx = fl in head sx + head sx
  Flattened version:
  let sx = fl
      c1 = head sx
      c2 = head sx
  in c1 + c2
  *)
  Definition doubleDeepSharedList `{I : Share} `{SA : ShareArgs} (P : Partial Shape Pos) (S : Strategy Shape Pos)
                        (f : FreeA -> FreeA -> FreeA)
                        (fl : Free Shape Pos (List Shape Pos A))
   : FreeA
  := @share Shape Pos I S (List Shape Pos A) _ fl >>= fun sx =>
     @call Shape Pos I S A (headList Shape Pos P sx) >>= fun c1 =>
     @call Shape Pos I S A (headList Shape Pos P sx) >>= fun c2 =>
              f c1 c2.

End SecFunctions.

(* Some notations for convenience.
   Since we only provide the sharing instance and functions when the handlers
   are called, the arguments Shape and Pos can be inferred. *)
Notation "'Cbneed_'" := (Cbneed _ _).
Notation "'Cbn_'" := (Cbn _ _).
Notation "'Cbv_'" := (Cbv _ _).
Notation "'addInteger_'" := (addInteger _ _).
Notation "'orBool_'" := (orBool _ _).


(* ---------------------- Test cases without sharing ----------------------- *)

(* 
0?1 + 0?1
= 0+0 ? 0+1 ? 1+0 ? 1+1
= 0 ? 1 ? 1 ? 2
*)

Example exAddNoSharingND : handle (doubleShared  Cbn_ addInteger_ (coin Cbn_))
                           = [0%Z;1%Z;1%Z;2%Z].
Proof. constructor. Qed.

(*
trace "One" 1 + trace "One" 1
=> The message should be logged twice and the result should be 2.
*)
Example exAddNoSharingTrace 
: handle (doubleShared Cbn_ addInteger_ traceOne)
  = (2%Z,["One"%string;"One"%string]).
Proof. constructor. Qed.

(*
(true ? false) or (true ? false)
= (true or (true ? false)) ? (false or (true ? false))
= true ? (true ? false)
= true ? true ? false
*)
Example exOrNDNoSharing 
 : handle (doubleShared Cbn_ orBool_ (coinB Cbn_)) = [true;true;false].
Proof. constructor. Qed.

(*
(trace "True" true) or (trace "True" true)
=> The second argument is not evaluated, so the result should be true and the 
   message should be logged only once.
*)
Example exOrTrueTracingNoSharing 
 : handle (doubleShared Cbn_ orBool_ traceTrue)
   = (true,["True"%string]).
Proof. constructor. Qed.

(*
(trace "False" false) or (trace "False" false)
=> Both arguments are evaluated, so the result should be false and the message
   should be logged twice.
*)
Example exOrFalseTracingNoSharing 
 : handle (doubleShared Cbn_ orBool_ traceFalse)
   = (false,["False"%string;"False"%string]).
Proof. constructor. Qed.

(*
(trace "False" false) or (trace "True" false)
=> Both arguments are evaluated, so the result should be true and both messages
   should be logged.
*)
Example exOrMixedTracingNoSharing
 : handle (orBool_ traceFalse traceTrue)
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
 : handle (doubleShared Cbn_ addInteger_ (coinM Cbn_)) = [None;None;Some 2%Z].
Proof. constructor. Qed.

(* 
trace "Nothing" Nothing + trace "Nothing" Nothing
=> The second argument is not evaluated due to >>=, so the message should
   only be logged once and the result should be Nothing (i.e. None in Coq).
*)
Example exTraceNothingNoSharing
 : handle (doubleShared Cbn_ addInteger_ traceNothing)
   = (None,["Nothing"%string]).
Proof. constructor. Qed.

(*
trace "Just 1" (Just 1) + trace "Just 1" (Just 1)
=> Since there is no sharing, the message should be logged twice and the 
   result should be Just 2 (Some 2 in Coq).
*)
Example exTraceJustNoSharing
 : handle (doubleShared Cbn_ addInteger_ traceJust)
   = (Some 2%Z,["Just 1"%string;"Just 1"%string]).
Proof. constructor. Qed.


(* --------------------- Test cases for simple sharing --------------------- *)

(*
let sx = 0 ? 1 
in sx + sx 
= 0+0 ? 1+1
= 0 ? 2
*)
Example exAddSharingND : handle (doubleShared Cbneed_
  addInteger_ (coin Cbneed_))
  = [0%Z;2%Z].
Proof. constructor. Qed.

(* Strict evaluation also leads to consistent choices. *)
Example exAddSharingNDStrict : handle (doubleShared Cbv_
  addInteger_ (coin Cbv_))
  = [0%Z;2%Z].
Proof. constructor. Qed.

(*
let sx = trace "One" 1
in sx + sx
=> The message should be logged once and the result should be 2.
*)
Example exAddSharingTrace 
 : handle (doubleShared Cbneed_ addInteger_ traceOne)
 = (2%Z,["One"%string]).
Proof. constructor. Qed.

(* Strict evaluation also leads to the message being logged only once. *)
Example exAddSharingTraceStrict
 : handle (doubleShared Cbv_ addInteger_ traceOne)
 = (2%Z,["One"%string]).
Proof. constructor. Qed.

(*
let sx = true ? false
in sx or sx
= (true or true) ? (false or false)
= true ? false
*)
Example exOrNDSharing
 : handle (doubleShared Cbneed_ orBool_ (coinB Cbneed_)) = [true;false].
Proof. constructor. Qed.

(* Strict evaluation also leads to consistent choices. *)
Example exOrNDSharingStrict
 : handle (doubleShared Cbv_ orBool_ (coinB Cbv_)) = [true;false].
Proof. constructor. Qed.

(*
let sx = trace "True" true
in sx or sx 
=> The second argument is not evaluated, so sharing makes no difference here.
   The message should be logged once and the result should be true.
*)
Example exOrTrueTraceSharing
 : handle (doubleShared Cbneed_ orBool_ traceTrue)
   = (true,["True"%string]).
Proof. constructor. Qed.

(* Strict evaluation also leads to the message being logged only once. *)
Example exOrTrueTraceSharingStrict
 : handle (doubleShared Cbv_ orBool_ traceTrue)
   = (true,["True"%string]).
Proof. constructor. Qed.

(*
let sx = trace "False" true
in sx or sx
=> Both arguments are evaluated, but sx is shared, so the message should
only be logged once and the result should be false.
*)
Example exOrFalseTraceSharing
 : handle (doubleShared Cbneed_ orBool_ traceFalse)
   = (false,["False"%string]).
Proof. constructor. Qed.

(*
let sx = Nothing ? Just 1
in sx + sx
= Nothing + Nothing ? Just 1 + Just 1
= Nothing ? Just 2
*)
Example exNDMSharing
 : handle (doubleShared Cbneed_ addInteger_ (coinM Cbneed_))
   = [None;Some 2%Z].
Proof. constructor. Qed.

(*
let sx = trace "Nothing" Nothing
in sx + sx
=> The message should only be logged once and the result should be Nothing
   due to >>=.
*)
Example exTraceNothingSharing
 : handle (doubleShared Cbneed_ addInteger_ traceNothing)
   = (None,["Nothing"%string]).
Proof. constructor. Qed.

(*
let sx = trace "Just 1" (Just 1)
in sx + sx 
=> The message should only be logged once due to sharing and the result 
   should be Some 2.
*)
Example exTraceJustSharing
 : handle (doubleShared Cbneed_ addInteger_ traceJust)
   = (Some 2%Z,["Just 1"%string]).
Proof. constructor. Qed.

(* --------------------- Test cases for nested sharing --------------------- *)

(* 
let sx = 0 ? 1 
    sy = sx + sx 
in sy + sy 
= (0+0)+(0+0) ? (1+1)+(1+1) 
= 0 ? 4 
*)
Example exAddNestedSharingND : handle (doubleSharedNested Cbneed_
                                                          addInteger_ 
                                                          (coin Cbneed_))
                               = [0%Z;4%Z].
Proof. constructor. Qed.

(* 
let sx = trace "One" 1
    sy = sx + sx 
in sy + sy 
=> The message should only be logged once and the result should be 4. 
*)
Example exAddNestedSharingTrace 
 : handle (doubleSharedNested Cbneed_ addInteger_ traceOne)
   = (4%Z,["One"%string]).
Proof. constructor. Qed.

(*
let sx = true ? false
    sy = sx or sx
in sy or sy
= true ? false
*)
Example exOrNestedSharingND
 : handle (doubleSharedNested Cbneed_ orBool_ (coinB Cbneed_))
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
 : handle (doubleSharedNested Cbneed_ orBool_ traceTrue)
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
 : handle (doubleSharedNested Cbneed_ orBool_ traceFalse)
   = (false, ["False"%string]).
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
 : handle (doubleSharedClash Cbneed_ addInteger_ (coin Cbneed_) (coin Cbneed_))
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
 : handle (doubleSharedClash Cbneed_ addInteger_
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
 : handle (doubleSharedClash Cbneed_ orBool_ (coinB Cbneed_) (coinB Cbneed_))
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
 : handle (doubleSharedClash Cbneed_ orBool_
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
 : handle (doubleSharedClash Cbneed_ orBool_
                                  traceFalse traceFalse)
   = (false,["False"%string;"False"%string]).
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
Example exAddRecSharingND : handle (doubleSharedRec Cbneed_
                                                    addInteger_
                                                    (coin Cbneed_) (coin Cbneed_) 1%Z)
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
 : handle (doubleSharedRec Cbneed_ addInteger_
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
 : handle (doubleSharedRec Cbneed_ orBool_ (coinB Cbneed_) (coinB Cbneed_) true)
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
 : handle ((doubleSharedRec Cbneed_ orBool_ (coinB Cbneed_) (coinB Cbneed_) false))
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
 : handle (doubleSharedRec Cbneed_ orBool_
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
 : handle (doubleSharedRec Cbneed_ orBool_
                                traceFalse traceFalse false)
   = (false,["False"%string;"False"%string]).
Proof. constructor. Qed.


(* ----------------------- Test cases for deep sharing --------------------- *)

(*
let sx = (0 ? 1, 2 ? 3)
in fst sx + fst sx

= (0 + 0) ? (1 + 1)
= 0 ? 2
*)
Example exAddDeepPairND
 : handle (doubleDeepSharedPair Cbneed_ addInteger_ (coinPair Cbneed_))
  = [0%Z;2%Z].
Proof. constructor. Qed.

(* let sx = [0 ? 1, 2 ? 3]
in head sx + head sx
= (0 + 0) ? (1 + 1)
= 0 ? 2
*)
Example exAddDeepListND
 : handle
  (doubleDeepSharedList (PartialLifted ND.Shape ND.Pos _ _ ND.Partial) 
   Cbneed_ addInteger_ (coinList Cbneed_))
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
 : handle (doubleDeepSharedPair Cbneed_ addInteger_ (tracePair Cbneed_))
  = (0%Z, ["0"%string]).
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
 : handle
   (doubleDeepSharedList (PartialLifted Maybe.Shape Maybe.Pos _ _ Maybe.Partial)
    Cbneed_ addInteger_ (traceList Cbneed_))
  = (Some 0%Z, ["0"%string]).
Proof. constructor. Qed.