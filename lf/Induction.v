Require Export Basics.


Example add_0_n :
  forall (n : nat), (plus O n) = n.
Proof.
  reflexivity.
Qed.


Theorem add_n_O :
  forall (n : nat), plus n O = n.
Proof.
  intros n.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    rewrite -> IHn'.
    reflexivity. 
Qed.

Theorem minus_n_n:
  forall (n : nat), minus n n = O.
Proof.
  induction n as [| n' IHn'].
  - reflexivity.
  - simpl.
    apply IHn'. 
Qed.


Lemma add_m_Sn:
  forall n m : nat, S (plus n m) = plus n (S m).
Proof.
  intros n m.
  induction n as [| n'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn'.
    reflexivity.
Qed.



Theorem add_commutative:
  forall (n m : nat), plus n m = plus m n.
Proof.
  intros.
  induction n as [| n'].
  - simpl.
    Check add_n_O.
    rewrite (add_n_O m).
    reflexivity.
  - simpl.
    rewrite IHn'. 
    rewrite add_m_Sn.
    reflexivity.
Qed.


Theorem mult_0_plus :
  forall n m : nat, (n + 0 + 0) * m = n * m.
Proof.
  intros n m.
  assert (H : n + 0 + 0 = n).
    {
      Set Printing Parentheses.
      rewrite add_commutative.
      simpl.
      rewrite add_commutative.
      reflexivity.
    }
  rewrite H.
  reflexivity.
Qed.


Theorem plus_rearrange :
  forall n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros.
  rewrite (add_commutative n m).
  reflexivity.
Qed.


Theorem plus_rearrange' :
  forall n m p q : nat, (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros.
  assert (H : n + m = m + n).
    {
      apply add_commutative.
    }
  rewrite H.
  reflexivity.
Qed.


Theorem plus_assoc :
  forall a b c : nat, (a + b) + c = a + (b + c).
Proof.
  intros a b c.
  induction a.
  - reflexivity.
  - simpl.
    rewrite IHa.
    reflexivity.
Qed.


