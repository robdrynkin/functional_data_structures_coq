(*|
=============================================
Queue
=============================================

:Authors: Ivan Rybin, Robert Drynkin
:Date: July 30, 2021

=============================================

|*)


Set Warnings "-extraction-opaque-accessed,-extraction,-notation-overridden".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq. (* coq-mathcomp-ssreflect *)
From Equations Require Import Equations. (* coq-equations *)
From QuickChick Require Import QuickChick. (* coq-quickchick *)
Import GenLow GenHigh. (* from QuickChick *)
From mathcomp Require Import zify. (* coq-mathcomp-zify *)
From deriving Require Import deriving. (* coq-deriving *)
From mathcomp.ssreflect Require Import tuple.
(* From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat. *)
From mathcomp Require Import seq choice fintype.

Set Equations Transparent.

Global Set Bullet Behavior "None".
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Queue.

(*|
Queue abstractions
---------------------------------------

IUnsafeQueue contains all necessary queue methods but doesn't give any guarantees about correctness.

|*)

Structure IUnsafeQueue {Q : Type -> Type} := MkUnsafeQueue {
    empty : forall {A}, Q A;
    isEmpty : forall {A}, Q A -> bool;
    push : forall {A}, Q A -> A -> Q A;
    head : forall {A}, Q A -> option A;
    tail : forall {A}, Q A -> Q A;
}.

(*| We will use list queue as a specification for other queues |*)

Definition ListQueue (A : Type) := seq A.

Definition listQueueImpl: @IUnsafeQueue ListQueue :=
{|
  empty := fun A => Nil A;
  isEmpty := fun A q => match q with | Nil _ => true | _ => false end;
  push := fun A q v => q ++ [:: v];
  head := fun A q => ohead q;
  tail := fun A q => match q with | Nil _ => Nil A | Cons _ x xs => xs end;
|}.


(*| A common representation for purely functional queues is as a pair of stacks f and r,
where f contains the front elements of the queue in the correct order and r contains
the rear elements of the queue in reverse order. For example, a queue containing the
integers 1..6 might be represented by the stacks f = [1, 2, 3] and r = [6, 5, 4].
This representation is described by the following datatype:
 |*)

Inductive TwoStackQueue (A : Type) := MkQueue (f r : seq A).
Derive (Arbitrary, Show) for TwoStackQueue.

Definition twoStackQueueUnsafeImpl: @IUnsafeQueue TwoStackQueue :=
{|
  empty := fun A => MkQueue (Nil A) (Nil A);
  isEmpty := (fun A q => match q with
    | MkQueue (Nil _) (Nil _) => true
    | _ => false
    end);
  push := (fun A q v => match q with
    | MkQueue f r => MkQueue f (v :: r)
    end);
  head := (fun A q => match q with
    | MkQueue (Cons _ x _) _ => Some x
    | MkQueue (Nil _)      r => ohead (rev r)
    end);
  tail := (fun A q => match q with
    | MkQueue (Nil _) t => MkQueue (behead (rev t)) (Nil A)
    | MkQueue (Cons _ _ xs) r    => MkQueue xs r
    end);
|}.

(*| Safe queue holds unfase queue method, projection to the specification model and proofs of correctness. |*)

Structure ISafeQueue {Q : Type -> Type} := MkSafeQueue {
    q :> @IUnsafeQueue Q;

    ToModel : forall {A}, Q A -> ListQueue A;

    CheckPush (A : Type) (x : A) (qq : Q A):
        ToModel (push q qq x) = (ToModel qq) ++ [:: x];
        
    CheckHead (A : Type) (x : A) (qq : Q A): 
        head q qq = head listQueueImpl (ToModel qq);
}.


Definition TwoStackQueueToModel (A : Type) (q : TwoStackQueue A) :=
  match q with
  | MkQueue f r => f ++ (rev r)
  end.

Lemma TwoStackQueuePushOk (A : Type) (x : A) (q : TwoStackQueue A):
    TwoStackQueueToModel (push twoStackQueueUnsafeImpl q x) = (TwoStackQueueToModel q) ++ [:: x].
Proof.
  case: q.
  move => f r.
  rewrite /push //=.
  rewrite rev_cons.
  rewrite -cats1 //=.
  rewrite catA.
  done.
Qed.


Lemma TwoStackQueueHeadOk (A : Type) (x : A) (q : TwoStackQueue A):
  head twoStackQueueUnsafeImpl q = head listQueueImpl (TwoStackQueueToModel q).
Proof.
  case: q.
  move => f r.
  rewrite /push //=.
  case: f.
  done.
  move => h t.
  by move => //=.
Qed.


Definition twoStackQueueImpl: @ISafeQueue TwoStackQueue :=
{|
  q := twoStackQueueUnsafeImpl;
  ToModel := TwoStackQueueToModel;
  CheckPush := TwoStackQueuePushOk;
  CheckHead := TwoStackQueueHeadOk;
|}.


(*| Lets add ala go notations |*)

Notation "<e>" := (empty twoStackQueueImpl) (at level 50, no associativity).
Notation "q <- x" := (push twoStackQueueImpl q x) (at level 50, no associativity).
Notation "q ->" := (tail twoStackQueueImpl q) (at level 50, no associativity).
Notation "<- q" := ((head twoStackQueueImpl q), (tail twoStackQueueImpl q)) (at level 50, no associativity).


Compute <e> <- 1 <- 2 <- 3.

Compute (
    let q := <e> <- 1 <- 2 <- 3 in
    <- q
).

Compute (
    let q0 := <e> <- 1 <- 2 <- 3 in
    let (a1, q1) := <- q0 in
    let (a2, q2) := <- q1 in
    let (a3, q3) := <- q2 in
    (a1, a2, a3, q3)
).

End Queue.
