From PLF Require Import Maps.
From Coq Require Import Bool.Bool.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat. Import Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Logic.FunctionalExtensionality.
From PLF Require Export Imp.

(* Behavioral Equivalence *)

Definition aequiv (a1 a2 : aexp) : Prop :=
  forall (st : state),
    aeval st a1 = aeval st a2.

Definition bequiv (b1 b2 : bexp) : Prop :=
  forall (st : state),
    beval st b1 = beval st b2.


Theorem aequiv_example :
  aequiv <{ X - X }> <{ 0 }>.
Proof.
  intros st.
  simpl.
  lia.
Qed.

Theorem bequiv_example :
  bequiv <{ X - X = 0 }> <{ true }>.
Proof.
  intros st.
  unfold beval.
  rewrite aequiv_example.
  reflexivity.
Qed.





