From Coq Require Import Lia.
From LF Require Import Maps.
From LF Require Import Imp.


Theorem ceval_deterministic :
  forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 E1 E2.
  generalize dependent st2.
  induction E1; intros st2 E2;
  inversion E2; subst.
  - reflexivity.
  - reflexivity.
  - rewrite (IHE1_1 st'0 H1) in *.
    apply IHE1_2.
    assumption.
  - apply IHE1.
    assumption.
  - rewrite H in H5.
    discriminate.
  - rewrite H in H5.
    discriminate.
  - apply IHE1.
    assumption.
  - reflexivity.
  - rewrite H in H2.
    discriminate.
  - rewrite H in H4.
    discriminate.
  - rewrite (IHE1_1 st'0 H3) in *.
    apply IHE1_2.
    assumption.
Qed.


Example auto_example_1 : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  intros P Q R H1 H2 H3.
  apply H2.
  apply H1.
  assumption.
Qed.


Example auto_example_1' : forall (P Q R: Prop),
  (P -> Q) -> (Q -> R) -> P -> R.
Proof.
  auto.
Qed.



Example auto_example_2 : forall P Q R S T U : Prop,
  (P -> Q) ->
  (P -> R) ->
  (T -> R) ->
  (S -> T -> U) ->
  ((P -> Q) -> (P -> S)) ->
  T ->
  P ->
  U.
Proof.
  auto.
Qed.


Example auto_example_3 : forall (P Q R S T U: Prop),
  (P -> Q) ->
  (Q -> R) ->
  (R -> S) ->
  (S -> T) ->
  (T -> U) ->
  P ->
  U.
Proof.
  auto.
  debug auto.
  auto 6.
Qed.


(* Some common lemmas about equality and logical
operators are installed in this hint database by default. *)

Example auto_example_4 : forall P Q R : Prop,
  Q ->
  (Q -> R) ->
  P \/ (Q /\ R).
Proof.
  auto.
Qed.


(* If we want to see which facts auto is using,
we can use info_auto instead.  *)

Example auto_example_5: 2 = 2.
Proof.
  info_auto.
Qed.


Example auto_example_5' : forall (P Q R S T U W: Prop),
  (U -> T) ->
  (W -> U) ->
  (R -> S) ->
  (S -> T) ->
  (P -> R) ->
  (U -> T) ->
  P ->
  T.
Proof.
  (* info_auto. *)
  intros.
  info_auto.
Qed.


Lemma le_antisym :
  forall n m: nat, (n <= m /\ m <= n) -> n = m.
Proof.
  lia.
Qed.


Example auto_example_6 : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  auto using le_antisym.
Qed.


Hint Resolve le_antisym : core.


Example auto_example_6' : forall n m p : nat,
  (n <= p -> (n <= m /\ m <= n)) ->
  n <= p ->
  n = m.
Proof.
  auto.
Qed.


Definition is_fortytwo x := (x = 42).

Hint Unfold is_fortytwo : core.


Example auto_example_7: forall x,
  (x <= 42 /\ 42 <= x) -> is_fortytwo x.
Proof.
  (* auto. *)
  info_auto.
Qed.



Theorem ceval_deterministic': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 H1 H2.
  generalize dependent st2.
  induction H1; intros st2 H2; inversion H2; subst; auto.
  - rewrite (IHceval1 st'0 H1) in *.
    auto.
  - rewrite H in H7.
    discriminate.
  - rewrite H in H7.
    discriminate.
  - rewrite H in H3.
    discriminate.
  - rewrite H in H5.
    discriminate.
  - rewrite (IHceval1 st'0 H4) in *.
    auto.
Qed.


Theorem ceval_deterministic'_alt: forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof with auto.
  intros c st st1 st2 H1 H2.
  generalize dependent st2.
  induction H1; intros st2 H2; inversion H2; subst...
  - rewrite (IHceval1 st'0 H1) in *...
  - rewrite H in H7.
    discriminate.
  - rewrite H in H7.
    discriminate.
  - rewrite H in H3.
    discriminate.
  - rewrite H in H5.
    discriminate.
  - rewrite (IHceval1 st'0 H4) in *...
Qed.


Ltac rwd H1 H2 :=
  rewrite H1 in H2 ; discriminate.


Theorem ceval_deterministic'': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof with auto.
  intros c st st1 st2 H1 H2.
  generalize dependent st2.
  induction H1; intros st2 H2; inversion H2; subst...
  - rewrite (IHceval1 st'0 H1) in *...
  - rwd H H7.
  - rwd H H7.
  - rwd H H3.
  - rwd H H5.
  - rewrite (IHceval1 st'0 H4) in *...
Qed.


Ltac find_rwd :=
  match goal with
  H1 : ?E = true,
  H2 : ?E = false
  |- _ => rwd H1 H2
  end.


Theorem ceval_deterministic''': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 H1 H2.
  generalize dependent st2.
  induction H1; intros st2 H2; inversion H2; subst;
  try find_rwd; auto.
  - rewrite (IHceval1 st'0 H1) in *.
    auto.
  - rewrite (IHceval1 st'0 H4) in *.
    auto.
Qed.


Ltac find_eqn :=
  match goal with
  H1 : forall x, ?P x -> ?L = ?R,
  H2 : ?P ?X
  |- _ => rewrite (H1 X H2) in *
end.


Theorem ceval_deterministic'''': forall c st st1 st2,
  st =[ c ]=> st1 ->
  st =[ c ]=> st2 ->
  st1 = st2.
Proof.
  intros c st st1 st2 H1 H2.
  generalize dependent st2.
  induction H1; intros st2 H2; inversion H2; subst;
  try find_rwd; try find_eqn; auto.
Qed.


Module Repeat.
  Inductive com : Type :=
  | CSkip
  | CAsgn (x : string) (v : aexp)
  | CSeq (c1 c2 : com)
  | CIf (b : bexp) (c1 c2 : com)
  | CWhile (b : bexp) (c : com)
  | CRepeat (c : com) (b : bexp).


  Notation "'repeat' x 'until' y 'end'" :=
    (CRepeat x y)
    (in custom com at level 0,
     x at level 99, y at level 99).
  Notation "'skip'" :=
    (CSkip)
    (in custom com at level 0).
  Notation "x ':=' y" :=
    (CAsgn x y)
    (in custom com at level 0,
     x constr at level 0, y at level 85).
  Notation "x ; y" :=
    (CSeq x y)
    (in custom com at level 90, right associativity).
  Notation "'if' x 'then' y 'else' z 'end'" :=
    (CIf x y z)
    (in custom com at level 89, x at level 99,
     y at level 99, z at level 99).
  Notation "'while' x 'do' y 'end'" :=
    (CWhile x y)
    (in custom com at level 89,
     x at level 99, y at level 99).
  
  Reserved Notation "st '=[' c ']=>' st'"
  (at level 40, c custom com at level 99,
   st' constr at next level).

  Inductive ceval : com -> state -> state -> Prop :=
  | E_Skip : forall st,
    st =[ skip ]=> st
  | E_Asgn : forall st n x a1,
    aeval st a1 = n ->
    st =[ x := a1 ]=> ( x !-> n ; st)
  | E_Seq : forall c1 c2 st st' st'',
    st =[ c1 ]=> st' ->
    st' =[ c2 ]=> st'' ->
    st =[ c1 ; c2 ]=> st''
  | E_IfTrue : forall b c1 c2 st st',
    beval st b = true ->
    st =[ c1 ]=> st' ->
    st =[ if b then c1 else c2 end ]=> st'
  | E_IfFalse : forall b c1 c2 st st',
    beval st b = false ->
    st =[ c2 ]=> st' ->
    st =[ if b then c1 else c2 end ]=> st'
  | E_WhileTrue : forall b c st st' st'',
    beval st b = true ->
    st =[ c ]=> st' ->
    st' =[ while b do c end ]=> st'' ->
    st =[ while b do c end ]=> st''
  | E_WhileFalse : forall b c st,
    beval st b = false ->
    st =[ while b do c end ]=> st
  | E_RepeatEnd : forall b c st st',
    st =[ c ]=> st' ->
    beval st' b = true ->
    st =[ repeat c until b end ]=> st'
  | E_RepeatLoop : forall b c st st' st'',
    st =[ c ]=> st' ->
    beval st' b = false ->
    st' =[ repeat c until b end ]=> st'' ->
    st =[ repeat c until b end ]=> st''
  where "st =[ c ]=> st'" := (ceval c st st').
  
  
  
  Theorem ceval_deterministic: forall c st st1 st2,
    st =[ c ]=> st1 ->
    st =[ c ]=> st2 ->
    st1 = st2.
  Proof with auto.
    intros c st st1 st2 H1 H2.
    generalize dependent st2.
    induction H1; intros st2 H2; inversion H2;
    subst; try find_eqn; try find_rwd...
  Qed.

End Repeat.



Example ceval_example1:
  empty_st =[
    X := 2;
    if (X <= 1)
      then Y := 3
      else Z := 4
    end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  apply E_Seq with (X !-> 2).
  - apply E_Asgn.
    simpl.
    reflexivity.
  - apply E_IfFalse.
    + simpl.
      reflexivity.
    + apply E_Asgn.
      simpl.
      reflexivity.
Qed.


Example ceval'_example1:
  empty_st =[
    X := 2;
    if (X <= 1)
      then Y := 3
      else Z := 4
    end
  ]=> (Z !-> 4 ; X !-> 2).
Proof.
  eapply E_Seq.
  - apply E_Asgn.
    reflexivity.
  - apply E_IfFalse.
    + simpl.
      reflexivity.
    + apply E_Asgn.
      simpl.
      reflexivity.
Qed.


Hint Constructors ceval : core.
Hint Transparent state total_map : core.


Example eauto_example : exists s',
  (Y !-> 1 ; X !-> 2) =[
    if (X <= Y)
      then Z := Y - X
      else Y := X + Z
    end
  ]=> s'.
Proof.
  info_eauto.
Qed.


Lemma silly1 :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (forall x y : nat, P x y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros P Q HP HQ.
  eapply HQ.
  apply HP.
Abort.


Lemma silly2 :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros.
  eapply H0.
  destruct H as [y H'].
  Fail apply H'.
Abort.


Lemma silly2_fixed :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros.
  destruct H as [y H'].
  eapply H0.
  apply H'.
Qed.


Lemma silly2_ssumption :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros.
  destruct H as [y H'].
  eapply H0.
  Fail assumption.
Abort.



Lemma silly2_eassumption :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros.
  destruct H.
  eapply H0.
  eassumption.
Qed.

Lemma silly2_eauto :
  forall (P : nat -> nat -> Prop) (Q : nat -> Prop),
  (exists y, P 42 y) ->
  (forall x y : nat, P x y -> Q x) ->
  Q 42.
Proof.
  intros.
  destruct H.
  eauto.
Qed.
