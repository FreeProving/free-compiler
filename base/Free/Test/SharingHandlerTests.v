From Base Require Import Free.

From Base Require Import Free.Instance.Comb.
From Base Require Import Free.Instance.Identity.
From Base Require Import Free.Instance.ND.
From Base Require Import Free.Instance.Share.
From Base Require Import Free.Instance.Trace.

From Base Require Import Free.Malias.

From Base Require Import Prelude.Bool.
From Base Require Import Prelude.Integer.

From Base Require Import Free.Util.Search.

Require Import Lists.List.
Import List.ListNotations.

(* Synonym for cbneed for better readability. *)
Definition share {A : Type} 
                 {Shape : Type} 
                 {Pos : Shape -> Type}
                 `{i : Injectable Share.Shape Share.Pos Shape Pos} 
                 (x : Free Shape Pos A) 
:= @cbneed A Shape Pos i x.

(* Synonyms for programs containing non-determinism. *)
Definition NDShape := (Comb.Shape Share.Shape (Comb.Shape ND.Shape Identity.Shape)). 
Definition NDPos := (Comb.Pos Share.Pos (Comb.Pos ND.Pos Identity.Pos)).
Definition NDProg (A : Type) := Free NDShape NDPos A.

(* Synonyms for programs containing tracing. *)
Definition TraceShape := (Comb.Shape Share.Shape (Comb.Shape Trace.Shape Identity.Shape)). 
Definition TracePos := (Comb.Pos Share.Pos (Comb.Pos Trace.Pos Identity.Pos)).
Definition TraceProg (A : Type) := Free TraceShape TracePos A.

(* Shortcut to evaluate a non-deterministic program to a result list.
   list. *)
Definition evalND {A : Type} (p : NDProg A) 
:= collectVals (run (runChoice (runNDSharing (0,0) p))).

(* Shortcut to evaluate a traced program to a result and a list of logged 
   messages. *)
Definition evalTracing {A : Type} (p : TraceProg A) 
:= collectMessages (run (runTracing (runTraceSharing (0,0) p))).

(* Non-deterministic integer. *)
Definition coin : NDProg (Integer NDShape NDPos)
:= pure 0%Z ? pure 1%Z.

(* Traced integer. *)
Definition traceOne : TraceProg (Integer TraceShape TracePos) 
:= trace "One" (pure 1%Z).

(* ---------------------- Test cases without sharing ----------------------- *)

(* This function applies the given binary function to the given argument
   twice and does not share the argument. *)
Definition double {Shape : Type}
                  {Pos : Shape -> Type}
                  {A : Type}
                  `{Injectable Share.Shape Share.Pos Shape Pos}
                  (f : forall (Shape : Type) (Pos : Shape -> Type),
                       Free Shape Pos A ->
                       Free Shape Pos A -> 
                       Free Shape Pos A)
                  (fx : Free Shape Pos A)
 : Free Shape Pos A
:= f Shape Pos fx fx.

(* 
0?1 + 0?1
= 0+0 ? 0+1 ? 1+0 ? 1+1
= 0 ? 1 ? 1 ? 2
*)
Example exAddNoSharingND : evalND (double addInteger coin) = [0%Z;1%Z;1%Z;2%Z].
Proof. constructor. Qed.

(*
trace "One" 1 + trace "One" 1
=> The message should be logged twice and the result should be 2.
*)
Example exAddNoSharingTrace 
: evalTracing (double addInteger traceOne) 
  = (2%Z,["One"%string;"One"%string]).
Proof. constructor. Qed.


(* --------------------- Test cases for simple sharing --------------------- *)

(* let sx = fx in f sx sx *)
Definition doubleShared {Shape : Type}
                        {Pos : Shape -> Type}
                        {A : Type}
                        `{Injectable Share.Shape Share.Pos Shape Pos}
                        (f : forall (Shape : Type) (Pos : Shape -> Type),
                             Free Shape Pos A ->
                             Free Shape Pos A -> 
                             Free Shape Pos A)
                        (fx : Free Shape Pos A)
 : Free Shape Pos A
:= share fx >>= fun sx => f Shape Pos sx sx.

(*
let sx = 0 ? 1 
in sx + sx 
= 0+0 ? 1+1
= 0 ? 2
*)
Example exAddSharingND : evalND (doubleShared addInteger coin) = [0%Z;2%Z].
Proof. constructor. Qed.

(*
let sx = trace "One" 1
in sx + sx
=> The message should be logged once and the result should be 2.
*)
Example exAddSharingTrace 
 : evalTracing (doubleShared addInteger traceOne) = (2%Z,["One"%string]).
Proof. constructor. Qed.

(* --------------------- Test cases for nested sharing --------------------- *)

(* let sx = fx 
       sy = f sx sx
   in f sy sy *)
Definition doubleSharedNested {Shape : Type}
                              {Pos : Shape -> Type}
                              {A : Type}
                              `{Injectable Share.Shape Share.Pos Shape Pos}
                             (f : forall (Shape : Type) (Pos : Shape -> Type),
                                  Free Shape Pos A ->
                                  Free Shape Pos A -> 
                                  Free Shape Pos A)
                                  (fx : Free Shape Pos A)
 : Free Shape Pos A
:= share (share fx >>= fun sx => f Shape Pos sx sx) >>= fun sy =>
   f Shape Pos sy sy.

(* 
let sx = 0 ? 1 
    sy = sx + sx 
in sy + sy 
= (0+0)+(0+0) ? (1+1)+(1+1) 
= 0 ? 4 
*)
Example exAddNestedSharingND : evalND (doubleSharedNested addInteger coin) 
                            = [0%Z;4%Z].
Proof. constructor. Qed.

(* 
let sx = trace "One" 1
    sy = sx + sx 
in sy + sy 
=> The message should only be logged once and the result should be 4. 
*)
Example exAddNestedSharingTrace 
 : evalTracing (doubleSharedNested addInteger traceOne) 
   = (4%Z,["One"%string]).
Proof. constructor. Qed.

(* let sx = fx  
       sy = f sx sx
       sz = fy
   in f sy sz *)
Definition doubleSharedClash {Shape : Type}
                             {Pos : Shape -> Type}
                             {A : Type}
                             `{Injectable Share.Shape Share.Pos Shape Pos}
                             (f : forall (Shape : Type) (Pos : Shape -> Type),
                                  Free Shape Pos A ->
                                  Free Shape Pos A -> 
                                  Free Shape Pos A)
                             (fx : Free Shape Pos A)
                             (fy : Free Shape Pos A)
 : Free Shape Pos A
:= share (share fx >>= fun sx => f Shape Pos sx sx) >>= fun sy =>
   share fy >>=  fun sz => f Shape Pos sy sz.

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
 : evalND (doubleSharedClash addInteger coin coin) = [0%Z;1%Z;2%Z;3%Z].
Proof. constructor. Qed.

(*
let sx = trace "One" 1
    sy = sx + sx
    sz = trace "One" 1
in sy + sz
=> The message should be logged twice and the result should be 3.
*)
Example exAddClashSharingTracing
 : evalTracing (doubleSharedClash addInteger traceOne traceOne) 
   = (3%Z,["One"%string;"One"%string]).
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
                           `{Injectable Share.Shape Share.Pos Shape Pos}
                           (f : forall (Shape : Type) (Pos : Shape -> Type),
                                Free Shape Pos A ->
                                Free Shape Pos A -> 
                                Free Shape Pos A)
                           (fx : Free Shape Pos A)
                           (fy : Free Shape Pos A)
                           (val : A)
 : Free Shape Pos A
:= share (pure val) >>= fun sx =>
   f Shape Pos sx (share (f Shape Pos sx fx) >>= fun sy => 
      f Shape Pos sy (share (f Shape Pos sy fy) >>= fun sz =>
        f Shape Pos sz (pure val)
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
Example exAddRecSharingND : evalND (doubleSharedRec addInteger coin coin 1%Z) 
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
 : evalTracing (doubleSharedRec addInteger traceOne traceOne 1%Z) 
   = (7%Z,["One"%string;"One"%string]).
Proof. constructor. Qed.

