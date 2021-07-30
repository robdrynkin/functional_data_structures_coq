(*|
=============================================
Stack
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

Module Stack.


(*|
Stack definition
---------------------------------------

|*)

Inductive Stack (A : Type) :=
    | Empty
    | Cons (x : A) (xs : Stack A).

Definition push (A : Type) (s : Stack A) (x : A) : (Stack A) := Cons x s.

Definition isEmpty (A : Type) (s : Stack A) : bool := match s with
| Empty _ => true
| _       => false
end.

Definition head (A : Type) (s : Stack A) : (option A) := match s with
| Empty _   => None
| Cons x xs => Some x
end.

Definition tail (A : Type) (s : Stack A) : (Stack A) := match s with
| Empty _   => Empty A
| Cons x xs => xs
end.


Definition reverse (A : Type) (s : Stack A) : (Stack A) :=
    let fix reverse' rs s := match s with
        | Empty _   => rs
        | Cons x xs => reverse' (Cons x rs) xs
        end
    in reverse' (Empty A) s.

Fixpoint size (A : Type) (s : Stack A) : nat := match s with
| Empty _   => 0
| Cons x xs => 1 + (size xs)
end.


(*|
Stack definition
---------------------------------------

|*)

Lemma StackIsFifo (A : Type) (s : Stack A) :
    forall x, head (push s x) = Some x.
Proof.
    move => //=.
Qed.

Lemma StackDoesntDropElements (A : Type) (s : Stack A):
    forall x, tail (push s x) = s.
Proof.
    move => //=.
Qed.

Lemma SizeIncrease1 (A : Type) (s : Stack A):
    forall x, size(push s x) = size s + 1.
Proof.
    rewrite /push //=.
    rewrite addnC.
    done.
Qed.

End Stack.

(*|
Stack Examples
---------------------------------------

|*)


Compute Stack.Cons 2 (Stack.Cons 1 (Stack.Empty nat)).
Compute Stack.reverse (Stack.Cons 2 (Stack.Cons 1 (Stack.Empty nat))).
Compute Stack.head (Stack.Cons 2 (Stack.Cons 1 (Stack.Empty nat))).
Compute Stack.tail (Stack.Cons 2 (Stack.Cons 1 (Stack.Empty nat))).
Compute (Stack.head (Stack.Empty nat)).
Compute Stack.tail (Stack.Empty nat).
