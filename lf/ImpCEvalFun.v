From Coq Require Import Lia.
From Coq Require Import Arith.Arith.
From Coq Require Import Arith.PeanoNat.
Import Nat.
From Coq Require Import Arith.EqNat.
From LF Require Import Imp Maps.


Fixpoint ceval_step1 (st : state) (c : com) : state :=
  match c with
  | <{ skip }> =>
    st
  | <{ l := a1 }> =>
    (l !-> aeval st a1; st)
  | <{ c1 ; c2 }> =>
    let st' := ceval_step1 st c1 in
    ceval_step1 st' c2
  | <{ if b then c1 else c2 end}> =>
    if (beval st b) then ceval_step1 st c1
    else ceval_step1 st c2
  | <{ while b do c end }> =>
    st
  end.


Fixpoint ceval_step2 (st : state) (c : com) (i : nat) : state :=
  match i with
  | 0 => empty_st
  | S i' =>
    match c with
    | <{ skip }> =>
      st
    | <{ l := x }> =>
      (l !-> (aeval st x) ; st)
    | <{ c1 ; c2 }> =>
      let st' :=  ceval_step2 st c1 i' in
      ceval_step2 st' c2 i'
    | <{ if b then c1 else c2 end }> =>
      if (beval st b) then ceval_step2 st c1 i'
      else ceval_step2 st c2 i'
    | <{ while b do c1 end }> =>
      if (beval st b) then
        let st' := ceval_step2 st c1 i' in
        ceval_step2 st' c i'
      else st
    end
  end.


Fixpoint ceval_step3 (st : state) (c : com) (i : nat)
                      : option state :=
  match i with
  | 0 => None
  | S i' =>
    match c with
    | <{ skip }> =>
      Some st
    | <{ l := x }> =>
      Some (l !-> (aeval st x); st)
    | <{ c1 ; c2 }> =>
      match ceval_step3 st c1 i' with
      | None => None 
      | Some st' => ceval_step3 st' c2 i'
    end
    | <{ if b then c1 else c2 end }> =>
      if (beval st b) then ceval_step3 st c1 i'
      else ceval_step3 st c1 i'
    | <{ while b do c1 end }> =>
      if (beval st b) then
        match ceval_step3 st c1 i' with
        | None => None
        | Some st' => ceval_step3 st' c i'
        end
      else Some st
    end
  end.


Notation "'LETOPT' x <== e1 'IN' e2" :=
  (match e1 with
   | None => None
   | Some x => e2
   end)
  (at level 60, right associativity).


Fixpoint ceval_step (st : state) (c : com) (i : nat)
                  : option state :=
  match i with
  | 0 => None
  | S i' =>
    match c with
    | <{ skip }> =>
      Some st
    | <{ l := x }> =>
      Some (l !-> (aeval st x); st)
    | <{ c1 ; c2 }> =>
      LETOPT st' <== ceval_step st c1 i' IN
      ceval_step st' c2 i'
    | <{ if b then c1 else c2 end }> =>
      if (beval st b) then ceval_step st c1 i'
      else ceval_step st c2 i'
    | <{ while b do c1 end }> =>
      if (beval st b) then
        LETOPT st' <== ceval_step st c1 i' IN
        ceval_step st' c i'
      else
        Some st
    end
  end.


Definition test_ceval (st : state) (c : com) :=
  match ceval_step st c 500 with
  | None => None
  | Some st' => Some (st' X, st' Y, st' Z)
  end.


Example example_test_ceval :
  test_ceval empty_st
  <{
    X := 2;
    if (X <= 1)
    then Y := 3
    else Z := 4
    end
  }> = Some (2, 0, 4).
Proof.
  reflexivity.
Qed.


Definition pup_to_n : com :=
  <{
    Y := 0;
    while (X > 0) do
      Y := Y + X;
      X := X - 1
    end
  }>.


Example pup_to_n_1 :
  test_ceval (X !-> 5) pup_to_n
  = Some (0, 15, 0).
Proof.
  reflexivity.
Qed.


Theorem ceval_step__ceval :
  forall c st st',
  (exists i, ceval_step st c i = Some st') ->
  st =[ c ]=> st'.
Proof.
  intros c st st' H.
  inversion H as [i E].
  clear H.
  generalize dependent st'.
  generalize dependent st.
  generalize dependent c.
  induction i as [|i'].
  - intros c st st' H.
    discriminate H.
  - intros c st st' H.
    destruct c; simpl; inversion H; subst; clear H.
    + apply E_Skip.
    + apply E_Asgn.
      reflexivity.
    + destruct (ceval_step st c1 i') eqn: EQ.
      * apply E_Seq with s.
        ** apply IHi'.
           assumption.
        ** apply IHi'.
           assumption. 
      * discriminate H1.
    + destruct (beval st b) eqn : EQ.
      * apply E_IfTrue.
        ** assumption.
        ** apply IHi'.
          assumption.
      * apply E_IfFalse.
        ** assumption.
        ** apply IHi'.
           assumption.
    + destruct (beval st b) eqn: EQ.
      * destruct (ceval_step st c i') eqn : EQ1.
        ** apply E_WhileTrue with s.
          ++ assumption.
          ++ apply IHi'.
             assumption.
          ++ apply IHi'.
             assumption.
        ** discriminate H1.
      * injection H1 as H1'.
        rewrite <- H1'.
        apply E_WhileFalse.
        assumption.
Qed.


Theorem ceval_step_more: forall i1 i2 st st' c,
  i1 <= i2 ->
  ceval_step st c i1 = Some st' ->
  ceval_step st c i2 = Some st'.
Proof.
  induction i1 as [|i1']; intros i2 st st' c H1 H2.
  - simpl in H2.
    discriminate H2.
  - destruct i2 as [|i2'].
    inversion H1.
    assert (H1' : i1' <= i2') by lia.
    destruct c.
    + simpl in H2.
      simpl.
      assumption.
    + simpl in H2.
      simpl.
      assumption.
    + simpl in H2.
      simpl.
      destruct (ceval_step st c1 i1') eqn: EQ.
      * apply (IHi1' i2') in EQ.
        rewrite EQ.
        apply IHi1'.
        assumption.
        assumption.
        assumption.
      * discriminate H2.
    + simpl in H2.
      simpl.
      destruct (beval st b) eqn: EQ.
      * destruct (ceval_step st c1 i1') eqn : EQ1.
        ** apply IHi1'.
           assumption.
           rewrite EQ1.
           assumption.
        ** discriminate H2.
      * apply IHi1'.
        assumption.
        assumption.
    + simpl in H2.
      simpl.
      destruct (beval st b) eqn : EQ.
      * destruct (ceval_step st c i1') eqn : EQ2.
        ** apply (IHi1' i2') in EQ2; try assumption.
           rewrite -> EQ2. apply IHi1'; try assumption.
        ** discriminate H2.
      * assumption.
Qed.


Theorem ceval__ceval_step: forall c st st',
  st =[ c ]=> st' ->
  exists i, ceval_step st c i = Some st'.
Proof.
intros c st st' Hce.
induction Hce.
Admitted.


Theorem ceval_and_ceval_step_coincide: forall c st st',
  st =[ c ]=> st'
  <-> exists i, ceval_step st c i = Some st'.
Proof.
Admitted.



Theorem ceval_deterministic' : forall c st st1 st2,
     st =[ c ]=> st1 ->
     st =[ c ]=> st2 ->
     st1 = st2.
Proof.
  intros c st st1 st2 H1 H2.
Admitted.

