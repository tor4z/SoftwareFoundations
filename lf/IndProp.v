From LF Require Export Logic.
From Coq Require Import Lia.


Fixpoint div2 (n : nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S n') => S (div2 n')
  end.

Definition f (n : nat) :=
  if even n then div2 n
  else (3 * n) + 1.


Fail Fixpoint reach_1_in (n : nat) : nat :=
  if n =? 1 then 0
  else 1 + reach_1_in (f n).
  (* since the argument to the recursive call,
  f n, is not "obviously smaller" than n. *)

Inductive reachs_1 : nat -> Prop :=
  | term_done : reachs_1 1
  | term_more (n : nat) : reachs_1 (f n) -> reachs_1 n.
  (* The number 1 reaches 1,
     and any number n reaches 1 if f n does. *)


Conjecture collatz : forall n, reachs_1 n.


Module LePlayground.

  (*
    The following definition says that there are two ways to
    show that one number is less than or equal to another:
    either observe that they are the same number, or, if the
    second has the form S m, give evidence that the first is
    less than or equal to m.
  *)

  Inductive le : nat -> nat -> Prop :=
    | le_n (n : nat) : le n n
    | le_S (n m : nat) : le n m -> le n (S m).

End LePlayground.

Inductive clos_trans {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
  | t_step (x y : X) :
    R x y -> clos_trans R x y
  | r_trans (x y z : X) :
    clos_trans R x y ->
    clos_trans R y z ->
    clos_trans R x z.


Inductive Perm3 {X : Type} : list X -> list X -> Prop :=
| perm3_swap12 (a b c : X) :
  Perm3 [a;b;c] [b;a;c]
| perm3_swap23 (a b c : X) :
  Perm3 [a;b;c] [a;c;b]
| perm3_trans (l1 l2 l3 : list X) :
  Perm3 l1 l2 -> Perm3 l2 l3 -> Perm3 l1 l3.


(*
This definition says:
- If l2 can be obtained from l1 by swapping the first and
  second elements, then l2 is a permutation of l1.
- If l2 can be obtained from l1 by swapping the second and
  third elements, then l2 is a permutation of l1.
- If l2 is a permutation of l1 and l3 is a permutation of
  l2, then l3 is a permutation of l1.
*)


Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(* We can think of this as defining a Coq property
ev : nat → Prop, together with "evidence constructors"
ev_0 : ev 0 and ev_SS : ∀ n, ev n → ev (S (S n)).  *)


Theorem ev_4 : ev 4.
Proof.
  apply ev_SS.
  apply ev_SS.
  apply ev_0.
Qed.


Theorem ev_4' : ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.


Theorem ev_plus4 :
  forall n, ev n -> ev (4 + n).
Proof.
  intros.
  simpl.
  apply ev_SS.
  apply ev_SS.
  apply H.
Qed.


Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros.
  induction n as [|n'].
  - simpl.
    apply ev_0.
  - simpl.
    apply ev_SS.
    apply IHn'.
Qed.


Theorem ev_4'' : ev 4.
Proof.
  apply (ev_SS 2 (ev_SS 0 ev_0)).
Qed.



Theorem ev_inversion :
  forall (n : nat),
  ev n -> (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
    intros n H.
    destruct H as [| n' H'] eqn : EQN.
    - left.
      reflexivity.
    - right.
      exists n'.
      split.
      + reflexivity.
      + apply H'.
Qed.

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof.
  intros n H.
  apply ev_inversion in H.
  destruct H as [HSS | HEX].
  - discriminate HSS.
  - destruct HEX as [n' [HSS HEV]].
    injection HSS as HSS'.
    rewrite HSS'.
    apply HEV.
Qed.

(* 
  Here, the inversion tactic can detect (1) that the first
  case, where n = 0, does not apply and (2) that the n'
  that appears in the ev_SS case must be the same as n.
  It includes an "as" annotation similar to destruct,
  allowing us to assign names rather than have Coq choose
  them.
*)

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n H.
  inversion H as [| n' H' Heq].
  - apply H'.
Qed.


Theorem evSS_ev'' : forall n,
  ev n -> ev (S (S n)).
Proof.
  intros n H.
  inversion H as [| n' H' Heq].
  - apply ev_SS.
    apply ev_0.
  - apply ev_SS.
    apply ev_SS.
    apply H'.
Qed.

Theorem one_not_even : ~ ev 1.
Proof.
  intros H.
  apply ev_inversion in H.
  destruct H as [| [n' [HSS HEV]]].
  - discriminate H.
  - discriminate HSS.
Qed. 

Theorem one_not_even' : ~ ev 1.
Proof.
  intros H.
  inversion H as [| n' HEV HEQ].
Qed.


Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  apply ev_inversion in H.
  destruct H as [| [n' [HSS HEV]]].
  - discriminate H.
  - injection HSS as HSS'.
    rewrite <- HSS' in HEV.
    inversion HEV as [| n'' H'' HEQ''].
    apply H''.
Qed.


Theorem SSSSev__even' : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H.
  inversion H as [| n' Hev Heq].
  inversion Hev as [| n'' Hev' Heq'].
  apply Hev'.
Qed.

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H.
  apply ev_inversion in H.
  destruct H as [| [n' [HSS HEV]]].
  - discriminate H.
  - injection HSS as HSS'.
    rewrite <- HSS' in HEV.
    apply ev_inversion in HEV.
    destruct HEV as [| [n'' [HSS'' HEV'']]].
    + discriminate H.
    + injection HSS'' as HSS'''.
      rewrite <- HSS''' in HEV''.
      inversion HEV'' as [| n''' H''' HEQ'''].
Qed.


Theorem ev5_nonsense' :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H.
  inversion H as [| n' H' HEQ'].
  inversion H' as [| n'' H'' HEV''].
  inversion H'' as [| n''' H''' HEV'''].
Qed.

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] -> [n] = [m].
Proof.
  intros n m o H.
  inversion H.
  reflexivity.
Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n H.
  discriminate H.
Qed.

Theorem inversion_ex2' : forall (n : nat),
  S n = O -> 2 + 2 = 5.
Proof.
  intros n H.
  inversion H.
Qed.

Definition Even x := exists n : nat, x = double n.

Lemma ev_Even_firsttry : forall n,
  ev n -> Even n.
Proof.
  unfold Even.
  intros n H.
  inversion H as [EQ' | n' E' EQ'].
  - exists 0.
    simpl.
    reflexivity.
  - assert (HE : (exists k', n' = double k') ->
                 (exists n0, S (S n') = double n0)).
    {
      intros [k' EQ''].
      exists (S k').
      simpl.
      rewrite EQ''.
      reflexivity.
    }
    apply HE.
    (* generalize dependent E'. *)
Abort.


Lemma ev_Even : forall n,
  ev n -> Even n.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - unfold Even.
    exists 0.
    reflexivity.
  - unfold Even.
    destruct IH as [k Hk].
    rewrite Hk.
    exists (S k).
    simpl.
    reflexivity.
Qed.


Theorem ev_Even_iff : forall n,
  ev n <-> Even n.
Proof.
  intros n.
  split.
  - intros H.
    apply ev_Even.
    apply H.
  - unfold Even.
    intros [k Hk].
    rewrite Hk.
    apply ev_double.
Qed.


Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m Hn Hm.
  induction Hn as [| n' E' IH'].
  - simpl.
    apply Hm.
  - simpl.
    apply ev_SS.
    apply IH'.
Qed. 


Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).


Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n.
  split.
  - intros H.
    induction H as [| | n'' m'' IH'].
    + apply ev_0.
    + apply ev_SS.
      apply ev_0.
    + apply ev_sum.
      * apply IHIH'.
      * apply IHev'1.
  - intros H.
    induction H as [| n' E' IH'].
    + apply ev'_0.
    + assert (HSS : S (S n') = 2 + n').
      {
        simpl.
        reflexivity.
      }
      rewrite HSS.
      apply ev'_sum.
      * apply ev'_2.
      * apply IH'.
Qed.


Theorem ev_sum_inv :
  forall n m : nat, ev (n + m) -> ev n /\ ev m.
Proof.
  intros n m H.
  induction n as [|n'].
  - simpl in H.
    split.
    + apply ev_0.
    + apply H.
  - induction m as [|m'].
    + Check add_commutative.
      rewrite add_commutative in H.
      simpl in H.
      split.
      * apply H.
      * apply ev_0.
Abort.






Theorem ev_ev__ev : forall n m,
  ev (n + m) -> ev n -> ev m.
  (* Hint: There are two pieces of evidence you could attempt to induct upon
      here. If one doesn't work, try the other. *)
Proof.
  intros n m.
  intros H.
  intros H'.
  induction H' as [| n' E' IH'].
  - simpl in H.
    apply H.
  - apply IH'.
    simpl in H.
Abort.


Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p Hnm Hnp.
  apply ev_sum.
Abort.


Module Playground.
  Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat) : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

  Notation "n <= m" := (le n m).

  Theorem test_le1 :
    3 <= 3.
  Proof.
    apply le_n.
  Qed.

  Theorem test_le2 :
    3 <= 6.
  Proof.
    repeat (apply le_S; try apply le_n).
  Qed.

  Theorem test_le3 :
    (2 <= 1) -> 2 + 2 = 5.
  Proof.
    intros H.
    inversion H.
    inversion H2.
Qed.

Definition lt (n m : nat) := le (S n) m.

Notation "m < n" := (lt n m).


End Playground.


Inductive total_relation : nat -> nat -> Prop :=
  .

Module R.
  
Inductive R : nat -> nat -> nat -> Prop :=
  | c1 : R 0 0 0
  | c2 m n o (H : R m n o) : R (S m) n (S o)
  | c3 m n o (H : R m n o) : R m (S n) (S o)
  | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
  | c5 m n o (H : R m n o) : R m n o.



End R.


(* A Digression on Notation *)

Module bin1.
  Inductive bin : Type :=
  | Z
  | B0 (n : bin)
  | B1 (n : bin).
End bin1.

Module bin2.
  Inductive bin : Type :=
  | Z : bin
  | B0 (n : bin) : bin
  | B1 (n : bin) : bin.
End bin2.

Module bin3.
  Inductive bin : Type :=
  | Z : bin
  | B0 : bin -> bin
  | B1 : bin -> bin.
End bin3.


Inductive reg_exp (T : Type) : Type :=
| EmptySet
| EmptyStr
| Char (t : T)
| App (r1 r2 : reg_exp T)
| Union (r1 r2 : reg_exp T)
| Star (r : reg_exp T).


Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.


Reserved Notation "s =~ re" (at level 80).


Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
    (H1 : s1 =~ re1)
    (H2 : s2 =~ re2)
    : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
    (H1 : s1 =~ re1)
    : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
    (H1 : s2 =~ re2)
    : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
    (H1 : s1 =~ re)
    (H2 : s2 =~ (Star re))
    : (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).


Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.


(* full *)
Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] (Char _ : reg_exp nat)
              [2] (Char _ : reg_exp nat)).
  - apply (MChar 1).
  - apply (MChar 2).
Qed.


Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H.
  inversion H.
Qed.




