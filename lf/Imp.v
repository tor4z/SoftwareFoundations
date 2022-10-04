From Coq Require Import Bool.Bool.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.EqNat. Import Nat.
From Coq Require Import Lia.
From Coq Require Import Lists.List. Import ListNotations.
From Coq Require Import Strings.String.
From LF Require Export Maps.

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
  | BNEq (a1 a2 : aexp)
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
    | BNEq a1 a2 => negb ((aeval a1) =? (aeval a2))
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
  | BNEq a1 a2 => BNEq (optimize_0plus a1) (optimize_0plus a2)
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


  Theorem aeval_iff_aevalR :
    forall a n, (a ==> n) <-> aeval a = n.
  Proof.
    intros a n.
    split.
    - intros H.
      induction H; simpl;
      (try rewrite IHaevalR1; try rewrite IHaevalR2; reflexivity).
    - intros H.
      generalize dependent n.
      induction a; simpl; intros; subst.
      + apply E_ANum.
      + apply E_APlus.
        apply IHa1. reflexivity.
        apply IHa2. reflexivity.
      + apply E_AMinus.
        apply IHa1. reflexivity.
        apply IHa2. reflexivity.
      + apply E_AMult.
        apply IHa1. reflexivity.
        apply IHa2. reflexivity.
  Qed.
  
  Theorem aeval_iff_aevalR' :
    forall a n, (a ==> n) <-> aeval a = n.
  Proof.
    split.
    - intros H.
      induction H; subst; reflexivity.
    - generalize dependent n.
      induction a; simpl; intros; subst; constructor;
      try apply IHa1; try apply IHa2; reflexivity.
  Qed.

  Reserved Notation "e '==>b' b" (at level 90, left associativity).

  Inductive bevalR : bexp -> bool -> Prop :=
    | E_BTrue : BTrue ==>b true
    | E_BFalse : BFalse ==>b false 
    | E_BEq (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) ->
      BEq a1 a2 ==>b (n1 =? n2)
    | E_BNeq (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) ->
      BNEq a1 a2 ==>b negb (n1 =? n2)
    | E_BLe (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) ->
      BLe a1 a2 ==>b (n1 <=? n2)
    | E_BGt (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) ->
      BGt a1 a2 ==>b negb (n1 <=? n2)
    | E_BNot (e : bexp) (b : bool) :
      (e ==>b b) ->
      BNot e ==>b negb b
    | E_BAnd (e1 e2 : bexp) (b1 b2 : bool) :
      (e1 ==>b b1) -> (e2 ==>b b2) ->
      BAnd e1 e2 ==>b andb b1 b2
    | E_BOr (e1 e2 : bexp) (b1 b2 : bool) :
      (e1 ==>b b1) -> (e2 ==>b b2) ->
      BOr e1 e2 ==>b orb b1 b2
    where "e '==>b' b" := (bevalR e b) : type_scope.

  Lemma beval_iff_bevalR :
    forall b bv, b ==>b bv <-> beval b = bv.
  Proof.
  Admitted.

End AExp.


Module aevalR_division.
  Inductive aexp : Type :=
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp)
  | ADiv (a1 a2 : aexp).

  Reserved Notation "e '==>' n"
    (at level 90, left associativity).
  
    Inductive aevalR : aexp -> nat -> Prop :=
    | E_ANum (n : nat) :
      (ANum n) ==> n
    | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) ->
      (APlus a1 a2) ==> (n1 + n2)
    | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) ->
      (AMinus a1 a2) ==> (n1 - n2)
    | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) ->
      (AMult a1 a2) ==> (n1 * n2)
    | E_ADiv (a1 a2 : aexp) (n1 n2 n3 : nat) :
      (a1 ==> n1) -> (a2 ==> n2) -> (n2 > 0) ->
      (mult n2 n3 = n1) ->
      (ADiv a1 a2) ==> n3
    where "e '==>' n" := (aevalR e n) : type_scope.
End aevalR_division.


Module aevalR_extended.
  Reserved Notation "e '==>' n" (at level 90, left associativity).

  Inductive aexp : Type :=
  | AAny
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

  Inductive aevalR : aexp -> nat -> Prop :=
  | E_AAny (n : nat) :
    AAny ==> n
  | E_ANum (n : nat) :
    (ANum n) ==> n
  | E_APlus (a1 a2 : aexp) (n1 n2 : nat) :
    (a1 ==> n1) -> (a2 ==> n2) -> 
    (APlus a1 a2) ==> (n1 + n2)
  | E_AMinus (a1 a2 : aexp) (n1 n2 : nat) :
    (a1 ==> n1) -> (a2 ==> n2) ->
    (AMinus a1 a2) ==> (n1 - n2)
  | E_AMult (a1 a2 : aexp) (n1 n2 : nat) :
    (a1 ==> n1) -> (a2 ==> n2) ->
    (AMult a1 a2) ==> (n2 * n2)
  where "e '==>' n" := (aevalR e n) : type_scope.


End aevalR_extended.

Definition state := total_map nat.


Inductive aexp : Type :=
| ANum (n : nat)
| AId (x : string)
| APlus (a1 a2 : aexp)
| AMinus (a1 a2 : aexp)
| AMult (a1 a2 : aexp).


Definition W : string := "W".
Definition X : string := "X".
Definition Y : string := "Y".
Definition Z : string := "Z".


Inductive bexp : Type :=
| BTrue
| BFalse
| BEq (a1 a2 : aexp)
| BNEq (a1 a2 : aexp)
| BLe (a1 a2 : aexp)
| BGt (a1 a2 : aexp)
| BNot (b : bexp)
| BOr (b1 b2 : bexp)
| BAnd (b1 b2 : bexp).


Coercion AId : string >-> aexp.
Coercion ANum : nat >-> aexp.

Declare Custom Entry com.
Declare Scope com_scope.


Notation "<{ e }>" :=
  (e)
  (at level 0, e custom com at level 99)
  : com_scope.
Notation "( x )" :=
  (x)
  (in custom com, x at level 99)
  : com_scope.
Notation "x" :=
  (x)
  (in custom com at level 0, x constr at level 0)
  : com_scope.
Notation "f x .. y" :=
  (.. (f x) .. y)
  (in custom com at level 0, only parsing,
   f constr at level 0, x constr at level 9,
   y constr at level 9)
  : com_scope.
Notation "x + y" :=
  (APlus x y)
  (in custom com at level 50, left associativity).
Notation "x - y" :=
  (AMinus x y)
  (in custom com at level 50, left associativity).
Notation "x * y" :=
  (AMult x y)
  (in custom com at level 40, left associativity).
Notation "'true'" :=
  (true)
  (at level 1).
Notation "'false'" :=
  (false)
  (at level 1).
Notation "'true'" :=
  (BTrue)
  (in custom com at level 1).
Notation "'false'" :=
  (BFalse)
  (in custom com at level 1).
Notation "x <= y" :=
  (BLe x y)
  (in custom com at level 70, no associativity).
Notation "x > y" :=
  (BGt x y)
  (in custom com at level 70, no associativity).
Notation "x = y" :=
  (BEq x y)
  (in custom com at level 70, no associativity).
Notation "x <> y" :=
  (BNEq x y)
  (in custom com at level 70, no associativity).
Notation "x '&&' y" :=
  (BAnd x y)
  (in custom com at level 80, left associativity).
Notation "x '||' y" :=
  (BOr x y)
  (in custom com at level 80, left associativity).
Notation "'~' y" :=
  (BNot y)
  (in custom com at level 75, right associativity).

Open Scope com_scope.


Definition example_aexp : aexp := <{ 3 + (X * 2) }>.
Definition example_bexp : bexp := <{ true && ~(X <= 4)}>.

Fixpoint aeval (st : state) (a : aexp) : nat :=
  match a with
  | ANum n => n
  | AId x => st x
  | <{a1 + a2}> => (aeval st a1) + (aeval st a2)
  | <{a1 - a2}> => (aeval st a1) - (aeval st a2)
  | <{a1 * a2}> => (aeval st a1) * (aeval st a2)
  end.


Fixpoint beval (st : state) (b : bexp) : bool :=
  match b with
  | BTrue => true
  | BFalse => false
  | <{ a1 = a2}> => (aeval st a1) =? (aeval st a2)
  | <{ a1 <> a2}> => negb ((aeval st a1) =? (aeval st a2))
  | <{ a1 <= a2}> => (aeval st a1) <=? (aeval st a2)
  | <{ a1 > a2}> => negb ((aeval st a1) <=? (aeval st a2))
  | <{ ~b }> => negb (beval st b)
  | <{b1 && b2}> => andb (beval st b1) (beval st b2)
  | <{b1 || b2}> => orb (beval st b1) (beval st b2)
  end.


Definition empty_st := (_ !-> 0).


Notation "x '!->' v" := (x !-> v; empty_st) (at level 100).


Example aexp1 :
  aeval (X !-> 5) <{3 + (X * 2)}> = 13.
Proof.
  reflexivity.
Qed.


Example aexp2 :
    aeval (X !-> 5 ; Y !-> 4) <{ Z + (X * Y) }>
  = 20.
Proof.
  reflexivity.
Qed.


Example bexp1 :
    beval (X !-> 5) <{ true && ~(X <= 4) }>
  = true.
Proof.
  reflexivity.
Qed.


Inductive com : Type :=
| CSkip
| CAsgn (x : string) (a : aexp)
| CSeq (c1 c2 : com)
| CIf (b : bexp) (c1 c2 : com)
| CWhile (b : bexp) (c : com).


Notation "'skip'" :=
  (CSkip)
  (in custom com at level 0)
  : com_scope.
Notation "x ':=' y" :=
  (CAsgn x y)
  (in custom com at level 0, x constr at level 0,
   y at level 85, no associativity)
  : com_scope.
Notation "x ';' y" :=
  (CSeq x y)
  (in custom com at level 90, right associativity)
  : com_scope.
Notation "'if' x 'then' y 'else' z 'end'" :=
  (CIf x y z)
  (in custom com at level 89, x at level 99,
   y at level 99, z at level 99)
  : com_scope.
Notation "'while' x 'do' y 'end'" :=
  (CWhile x y)
  (in custom com at level 89, x at level 99, y at level 99)
  : com_scope.


Definition fact_in_coq : com :=
  <{
    Z := X;
    Y := 1;
    while Z <> 0 do
      Y := Y * Z;
      Z := Z - 1
    end
  }>.


Print fact_in_coq.


Unset Printing Notations.
Print fact_in_coq.
Set Printing Notations.


Print example_bexp.
Set Printing Coercions.
Print example_bexp.
Print fact_in_coq.
Unset Printing Coercions.


Locate aexp.
Locate "&&".
Locate "||".
Locate ";".
Locate "while".


Definition plus2 : com :=
  <{ X := X + 2 }>.

Definition XtimesYinZ : com :=
  <{ Z := X * Y }>.

Definition substract_slowly_body : com :=
  <{
    Z := Z - 1;
    X := X -1
  }>.


Definition substract_slowly : com :=
  <{
    while X <> 0 do
      substract_slowly_body
    end
  }>.


Definition substract_3_from_5_slowly : com :=
  <{
    X := 3;
    Z := 5;
    substract_slowly
  }>.


Definition loop : com :=
  <{
    while true do
      skip
    end
  }>.


Fixpoint ceval_fun_not_while (st : state) (c : com) : state :=
  match c with
  | <{ skip }>
    => st
  | <{ x := a }>
    => (x !-> (aeval st a); st)
  | <{ c1 ; c2 }>
    => let st' := ceval_fun_not_while st c1 in
       ceval_fun_not_while st' c2
  | <{ if b then c1 else c2 end }>
    => if (beval st b) then ceval_fun_not_while st c1
       else ceval_fun_not_while st c2
  | <{ while b do c end }>
    => st (* TODO *)
  end.


Reserved Notation "st '=[' c ']=>' st'"
  (at level 40, c custom com at level 99,
   st constr, st' constr at next level).

Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st, st =[ skip ]=> st
  | E_Asgn : forall st a n x,
             aeval st a = n ->
             st =[ x := a ]=> (x !-> n; st)
  | E_Seq : forall st st' st'' c1 c2,
             st =[ c1 ]=> st' ->
             st' =[ c2 ]=> st'' ->
             st =[c1 ; c2]=> st''
  | E_IfTrue : forall st st' b c1 c2,
             beval st b = true ->
             st =[ c1 ]=> st' ->
             st =[if b then c1 else c2 end]=> st'
  | E_IfFalse : forall st st' b c1 c2,
             beval st b = false ->
             st =[ c2 ]=> st' ->
             st =[if b then c1 else c2 end]=> st'
  | E_WhileFalse : forall st b c,
             beval st b = false ->
             st =[while b do c end]=> st
  | E_WhileTrue : forall st st' st'' b c,
             beval st b = true ->
             st =[ c ]=> st' ->
             st' =[while b do c end]=> st'' ->
             st =[while b do c end]=> st''
  where "st '=[' c ']=>' st'" := (ceval c st st').


Example ceval_example1 :
  empty_st =[
    X := 2;
    if (X <= 1) then Y := 3
    else Z := 4
    end
  ]=> (Z !-> 4; X !-> 2).
Proof.
  apply E_Seq with (X !-> 2). (* The intermidiate state *)
  - apply E_Asgn.
    reflexivity.
  - apply E_IfFalse.
    reflexivity.
    apply E_Asgn.
    reflexivity.
Qed.



Example ceval_example2:
  empty_st =[
    X := 0;
    Y := 1;
    Z := 2
  ]=> (Z !-> 2 ; Y !-> 1 ; X !-> 0).
Proof.
  apply E_Seq with (X !-> 0).
  - apply E_Asgn.
    reflexivity.
  - apply E_Seq with (Y !-> 1; X !-> 0).
    + apply E_Asgn.
      reflexivity.
    + apply E_Asgn.
      reflexivity.
Qed.


Set Printing Implicit.
Check @ceval_example2.


Definition pup_to_n : com :=
  <{
    Y := 0;
    while X <> 0 do
      Y := Y + X;
      X := X - 1
    end
  }>.


Theorem pup_to_2_ceval :
  (X !-> 2) =[
    pup_to_n
  ]=> (X !-> 0 ; Y !-> 3 ; X !-> 1 ; Y !-> 2 ; Y !-> 0 ; X !-> 2).
Proof.
  unfold pup_to_n.
  apply E_Seq with (Y !-> 0 ; X !-> 2).
  - apply E_Asgn.
    reflexivity.
  - apply E_WhileTrue with (X !-> 1 ;Y !-> 2; Y !-> 0; X !-> 2).
    + reflexivity.
    + apply E_Seq with (Y !-> 2; Y !-> 0; X !-> 2).
      * apply E_Asgn.
        reflexivity.
      * apply E_Asgn.
        reflexivity.
    + apply E_WhileTrue with (X !-> 0 ;Y !-> 3 ;X !-> 1 ;Y !-> 2; Y !-> 0; X !-> 2).
      * reflexivity.
      * apply E_Seq with (Y !-> 3 ;X !-> 1 ;Y !-> 2; Y !-> 0; X !-> 2).
        ** apply E_Asgn.
           reflexivity.
        ** apply E_Asgn.
           reflexivity.
      * apply E_WhileFalse.
        reflexivity.
Qed.


Theorem ceval_deterministic: forall c st st1 st2,
     st =[ c ]=> st1 ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2; inversion E2; subst.
  - reflexivity.
  - reflexivity.
  - rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2.
    assumption.
  - apply IHE1.
    assumption.
  - apply IHE1.
    rewrite H in H5.
    discriminate.
  - apply IHE1.
    rewrite H in H5.
    discriminate.
  - apply IHE1.
    apply H6.
  - reflexivity.
  - rewrite H in H2.
    discriminate.
  - rewrite H in H4.
    discriminate.
  - rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2.
    assumption.
Qed.


Theorem plus2_spec : forall st n st',
  st X = n ->
  st =[ plus2 ]=> st' ->
  st' X = n + 2.
Proof.
  intros.
  inversion H0.
  subst.
  simpl.
  apply t_update_eq.
Qed.


Module StackMachine.
  Inductive sinstr : Type :=
  | SPush (n : nat)
  | SLoad (x : string)
  | SPlus
  | SMinus
  | SMult.


  Fixpoint s_execute (st : state) (stack : list nat) (prog : list sinstr)
          : list nat :=
  match prog with
  | [] => stack
  | (SPush n) :: prog' => s_execute st (n :: stack) prog'
  | (SLoad x) :: prog' => s_execute st ((st x) :: stack) prog'
  | SPlus :: prog' => 
    let stack'' := match stack with
    | [] => []
    | [a] => [a]
    | a :: b :: stack' => (a + b) :: stack'
    end in
    s_execute st stack'' prog'
  | SMinus :: prog' =>
    let stack'' := match stack with
    | [] => []
    | [a] => [a]
    | a :: b :: stack' => (b - a) :: stack'
    end in
    s_execute st stack'' prog'
  | SMult :: prog' => 
    let stack'' := match stack with
    | [] => []
    | [a] => [a]
    | a :: b :: stack' => (a * b) :: stack'
    end in
    s_execute st stack'' prog'
  end.


  Check s_execute.


  Example s_execute1 :
    s_execute empty_st []
    [SPush 5; SPush 3; SPush 1; SMinus]
    = [2; 5].
  Proof.
    simpl.
    reflexivity.
  Qed.


  Example s_execute2 :
    s_execute (X !-> 3) [3;4]
    [SPush 4; SLoad X; SMult; SPlus]
    = [15; 4].
  Proof.
    simpl.
    reflexivity.
  Qed.

  Fixpoint s_compile (e : aexp) : list sinstr :=
    match e with
    | ANum n => [SPush n]
    | AId x => [SLoad x]
    | <{ a1 + a2}> =>
      (s_compile a1) ++ (s_compile a2) ++ [SPlus]
    | <{ a1 - a2 }> =>
      (s_compile a1) ++ (s_compile a2) ++ [SMinus]
    | <{ a1 * a2 }> =>
      (s_compile a1) ++ (s_compile a2) ++ [SMult]
    end.

  Example s_compile1 :
    s_compile <{ X - (2 * Y) }>
    = [SLoad X; SPush 2; SLoad Y; SMult; SMinus].
  Proof.
    simpl.
    reflexivity.
  Qed.

  Lemma s_compile_correct_aux : forall st e stack,
    s_execute st stack (s_compile e) = aeval st e :: stack.
  Proof.
    intros st e.
    induction e.
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
    - intros stack.
      simpl.
  Admitted.


  Theorem s_compile_correct : forall (st : state) (e : aexp),
    s_execute st [] (s_compile e) = [ aeval st e ].
  Proof.
  Admitted.

End StackMachine.


Module BreakImp.

  Inductive com : Type :=
  | CSKip
  | CBreak
  | CAsgn (x : string) (a : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com).

  Notation "'break'" :=
    (CBreak)
    (in custom com at level 0)
    : com_scope.
  Notation "'skip'" :=
    (CSkip)
    (in custom com at level 0)
    : com_scope.
  Notation "x ':=' y" :=
    (CAsgn x y)
    (in custom com at level 0, x constr at level 0,
     y at level 85, no associativity)
    : com_scope.
  Notation "x ; y" :=
    (CSeq x y)
    (in custom com at level 90, right associativity)
    : com_scope.
  Notation "'if' x 'then' y 'else' z 'end'" :=
    (CIf x y z)
    (in custom com at level 89, x at level 99,
     y at level 99, z at level 99)
    : com_scope.
  Notation "'while' x 'do' y 'end'" :=
    (CWhile x y)
    (in custom com at level 89,
     x at level 99, y at level 99)
    : com_scope.
  
  Inductive result : Type :=
  | SContinue
  | SBreak.
  
  Reserved Notation "st '=[' c ']=>' st' '/' s"
    (at level 40, c custom com at level 99,
     st' constr at next level).
  
  Inductive ceval : com -> state -> result -> state -> Prop :=
    | E_Skip : forall st,
      st =[ CSKip ]=> st / SContinue
    where "st '=[' c ']=>' st' '/' s" := (ceval c st s st').
  
  

End BreakImp.

