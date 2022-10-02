From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.


Module AExp.
  (* Abstract syntax *)
  Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

  (* Bool expression *)
  Inductive bexp : Type :=
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bexp)
  | BOr (b1 b2 : bexp)
  | BAnd (b1 b2 : bexp).

  Fixpoint aeval (a : aexp) : nat :=
    match a with
    | ANum n => n
    | APlus a1 a2 => (aeval a1) + (aeval a2)
    | AMinus a1 a2 => (aeval a1) - (aeval a2)
    | AMult a1 a2 => (aeval a1) * (aeval a2)
    end.

  Example test_aeval :
    aeval (APlus (ANum 2) (ANum 2)) = 4.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Fixpoint beval (b : bexp) : bool :=
    match b with
    | BTrue => true
    | BFalse => false
    | BEq a1 a2 => (aeval a1) =? (aeval a2)
    | BNeq a1 a2 => negb ((aeval a1) =? (aeval a2))
    | BLe a1 a2 => (aeval a1) <=? (aeval a2)
    | BGt a1 a2 => negb ((aeval a1) <=? (aeval a2))
    | BNot b => negb (beval b)
    | BAnd b1 b2 => andb (beval b1) (beval b1)
    | BOr b1 b2 => orb (beval b1) (beval b1)
    end.

  Fixpoint optimize_0plus (a : aexp) : aexp :=
    match a with
    | ANum n => ANum n
    | APlus (ANum 0) a2 => optimize_0plus a2
    (* | APlus a1 (ANum 0) => optimize_0plus a1 *)
    | APlus a1 a2 => APlus (optimize_0plus a1) (optimize_0plus a2)
    | AMinus a1 a2 => AMinus (optimize_0plus a1) (optimize_0plus a2)
    | AMult a1 a2 => AMult (optimize_0plus a1) (optimize_0plus a2)
    end.

  Example test_optimize_0plus :
    optimize_0plus (APlus (ANum 2)
                      (APlus (ANum 0)
                        (APlus (ANum 0) (ANum 1))))
    = APlus (ANum 2) (ANum 1).
  Proof.
    simpl.
    reflexivity.
  Qed.

  Theorem optimize_0plus_sound:
    forall a : aexp, aeval (optimize_0plus a) = aeval a.
  Proof.
    intros a.
    induction a.
    - simpl.
      reflexivity.
    - destruct a1 eqn: E1.
      + destruct n eqn: En.
        * simpl.
          rewrite IHa2.
          reflexivity.
        * simpl.
          rewrite IHa2.
          reflexivity.
      + simpl.
        simpl in IHa1.
        rewrite IHa1.
        rewrite IHa2.
        reflexivity.
      + simpl. 
        rewrite IHa2.
        simpl in IHa1.
        rewrite IHa1.
        reflexivity.
      + simpl.
        rewrite IHa2.
        simpl in IHa1.
        rewrite IHa1.
        reflexivity.
    - simpl.
      rewrite IHa1.
      rewrite IHa2.
      reflexivity.
    - simpl.
      rewrite IHa1.
      rewrite IHa2.
      reflexivity.
Qed.


Theorem silly1 :
  forall ae, aeval ae = aeval ae.
Proof.
  try reflexivity.
Qed.


Theorem silly2 :
  forall (P : Prop), P -> P.
Proof.
  intros P H.
  try reflexivity.
  apply H.
Qed.

Lemma foo : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.

Lemma foo' : forall n, 0 <=? n = true.
Proof.
  intros.
  destruct n;
  simpl;
  reflexivity.
Qed.

Theorem optimize_0plus_sound': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
  try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  - reflexivity.
  - destruct a1 eqn: Ea1;
    try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
    + destruct n eqn : En;
      simpl; rewrite IHa2; reflexivity.
Qed.

Theorem optimize_0plus_sound'': forall a,
  aeval (optimize_0plus a) = aeval a.
Proof.
  intros a.
  induction a;
  try (simpl; rewrite IHa1; rewrite IHa2; reflexivity).
  try reflexivity.
  - destruct a1;
    try (simpl; simpl in IHa1; rewrite IHa1; rewrite IHa2; reflexivity).
    + destruct n;
      try (simpl; rewrite IHa2; reflexivity).
Qed.


Theorem In10 : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat (try (left; reflexivity); right).
Qed.


Theorem In10' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  (* left. *)
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  right.
  left.
  reflexivity.
Qed.


Theorem In10'' : In 10 [1;2;3;4;5;6;7;8;9;10].
Proof.
  repeat simpl.
  repeat (left; reflexivity).
  repeat (right; try (left; reflexivity)).
Qed.


Theorem repeat_loop : forall (m n : nat),
  m + n = n + m.
Proof.
  intros m n.
  (* repeat rewrite Nat.add_comm. *)
  repeat (rewrite Nat.add_comm; reflexivity).
Qed.


Fixpoint optimize_0plus_b (b : bexp) : bexp :=
  match b with
  | BTrue => BTrue
  | BFalse => BFalse
  | BEq a1 a2 => BEq (optimize_0plus a1) (optimize_0plus a2)
  | BNeq a1 a2 => BNeq (optimize_0plus a1) (optimize_0plus a2)
  | BLe a1 a2 => BLe (optimize_0plus a1) (optimize_0plus a2)
  | BGt a1 a2 => BGt (optimize_0plus a1) (optimize_0plus a2)
  | BNot b => BNot (optimize_0plus_b b)
  | BOr b1 b2 => BOr (optimize_0plus_b b1) (optimize_0plus_b b2)
  | BAnd b1 b2 => BAnd (optimize_0plus_b b1) (optimize_0plus_b b2)
  end.

Theorem optimize_0plus_b_sound : forall b,
  beval (optimize_0plus_b b) = beval b.
  Proof.
    intros b.
    induction b;
    simpl;
    repeat reflexivity;
    repeat (rewrite optimize_0plus_sound;
            rewrite optimize_0plus_sound; reflexivity);
    repeat (rewrite IHb; reflexivity);
    repeat (rewrite IHb1; reflexivity).
Qed.


(** TODO
  Design exercise: The optimization implemented by our optimize_0plus
  function is only one of many possible optimizations on arithmetic
  and boolean expressions. Write a more sophisticated optimizer and
  prove it correct. (You will probably find it easiest to start small
  -- add just a single, simple optimization and its correctness proof
  -- and build up incrementally to something more interesting.)
*)


Ltac invert H := inversion H; subst; clear H.


Lemma invert_example1:
  forall {a b c: nat}, [a ;b] = [a;c] -> b = c.
Proof.
  intros.
  invert H.
  reflexivity.
Qed.

Lemma invert_example1':
  forall {a b c: nat}, [a ;b] = [a;c] -> b = c.
Proof.
  intros.
  inversion H. subst. clear H.
  reflexivity.
Qed.

Example silly_presburger_example :
  forall m n o p : nat, m + n <= n + O /\ O + 3 = p + 3 -> m <= p.
Proof.
  intros.
  lia.
Qed.



Example add_comm__lia : forall m n,
    m + n = n + m.
Proof.
  intros.
  lia.
Qed.

Example add_assoc__lia : forall m n p,
    m + (n + p) = m + n + p.
Proof.
  intros.
  lia.
Qed.


Module aevalR_first_try.

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) : aevalR (ANum n) n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
    aevalR e1 n1 -> aevalR e2 n2 -> aevalR (APlus e1 e2) (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
    aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMinus e1 e2) (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
    aevalR e1 n1 -> aevalR e2 n2 -> aevalR (AMult e1 e2) (n1 * n2).

  Module HypothesisNames.
    Inductive aevalR : aexp -> nat -> Prop :=
    | E_ANum (n : nat) : aevalR (ANum n) n
    | E_APlus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1) (H2 : aevalR e2 n2) :
      aevalR (APlus e1 e2) (n1 + n2)
    | E_AMinus (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1) (H2 : aevalR e2 n2) :
      aevalR (AMinus e1 e2) (n1 - n2)
    | E_AMult (e1 e2 : aexp) (n1 n2 : nat)
      (H1 : aevalR e1 n1) (H2 : aevalR e2 n2) :
      aevalR (AMult e1 e2) (n1 * n2).
  End HypothesisNames.
  
  Notation "e '==>' n" :=
    (aevalR e n)
    (at level 90, left associativity)
    : type_scope.

End aevalR_first_try.


Reserved Notation "e '==>' n"
  (at level 90, left associativity).

Inductive aevalR : aexp -> nat -> Prop :=
  | E_ANum (n : nat) : (ANum n) ==> n
  | E_APlus (e1 e2 : aexp) (n1 n2 : nat) :
    (e1 ==> n1) -> (e2 ==> n2) ->
    (APlus e1 e2) ==> (n1 + n2)
  | E_AMinus (e1 e2 : aexp) (n1 n2 : nat) :
    (e1 ==> n1) -> (e2 ==> n2) ->
    (AMinus e1 e2) ==> (n1 - n2)
  | E_AMult (e1 e2 : aexp) (n1 n2 : nat) :
    (e1 ==> n1) -> (e2 ==> n2) ->
    (AMult e1 e2) ==> (n1 * n2)
  where "e '==>' n" := (aevalR e n) : type_scope.


End AExp.