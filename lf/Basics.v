Check true.

Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.


Definition next_weekday (d : day) : day :=
  match d with
  | monday => tuesday
  | tuesday => wednesday
  | wednesday => thursday
  | thursday => friday
  | friday => saturday
  | saturday => sunday
  | sunday => monday
  end.


Compute next_weekday monday.

Example test_next_weekday :
  (next_weekday (next_weekday sunday)) = tuesday.
Proof.
  simpl.
  reflexivity.
Qed.


Inductive bool : Type :=
  | true
  | false.


Definition negb (b : bool) : bool :=
  match b with
    | true => false
    | false => true
  end.


Definition andb (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.


Definition orb (b1 b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.


Example test_orb_true_false :
  (orb true false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_orb_true_true :
  (orb true true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_orb_false_false :
  (orb false false) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_orb_false_true :
  (orb false true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_negb_false :
  (negb false) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_negb_true :
  (negb true) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example andb_true_true :
  (andb true true) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example andb_true_false :
  (andb true false) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example andb_false_true :
  (andb false true) = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example andb_false_false :
  (andb false false) = false.
Proof.
  simpl.
  reflexivity.
Qed.


Notation "x && y" := (andb x y).
Notation "x || y" := (orb x y).


Compute (true || false).
Compute (true && false).


Definition negb' (b : bool) : bool :=
  if b then false
  else true.


Definition orb' (b1 b2 : bool) : bool :=
  if b1 then true
  else b2.


Definition nandb (b1 b2 : bool) : bool :=
  negb (andb b1 b2).


Definition nandb' (b1 b2 : bool) : bool :=
  match b1 with
  | false => true
  | true =>
    match b2 with
    | true => false
    | false => true
    end
  end.



Example nanb_true_true :
  (nandb true true) = false.
Proof.
  (* compute. *)
  reflexivity.
Qed.

Example andb_true_true' :
  (nandb' true true) = false.
Proof.
  simpl.
  reflexivity.
Qed.
  

Check true : bool.
Check negb : bool -> bool.


(* ------------ *)

Inductive rgb : Type :=
  | red
  | green
  | blue.


Inductive color : Type :=
  | black
  | white
  | primary (p: rgb).


Definition monochrome (c : color) : bool :=
  match c with
  | black => true
  | white => true
  | primary p => false
  end.


Definition is_red (c : color) : bool :=
  match c with
  | white => false
  | black => false
  | primary red => true
  | primary _ => false
  end.


Module Playground.
  Definition b : rgb := blue.
End Playground.

  Definition b : bool := true.

Check b : bool.
Check Playground.b : rgb.
  

Module NatNumber.
  Inductive nat : Type :=
    | O
    | S (n : nat).
  
  Definition pred (n : nat) : nat :=
    match n with
    | O => O
    | S n' => n'
    end.
End NatNumber.

Check (S (S (S (S (S O))))).


Definition minustwo (n : nat) : nat :=
  match n with
  | O => O
  | S O => O
  | S (S n') => n'
  end.

Compute (minustwo 4).


Fixpoint even (n : nat) : bool :=
  match n with
  | O => true
  | S O => false
  | S (S n') => even n'
  end.

Fixpoint odd (n : nat) : bool :=
  match n with
  | O => false
  | S O => true
  | S (S n') => odd n'
  end.

Compute even 4.
Compute odd 3.

Example test_even_4 :
  (even 4) = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_odd_3 :
  (odd 3) = true.
Proof.
  simpl.
  reflexivity.
Qed.


Module NatNumber2.
  Fixpoint plus (n1 n2 : nat) : nat :=
    match n1 with
    | O => n2
    | S n1' => S (plus n1' n2)
    end.

  Compute (plus 3 4).

  Fixpoint mult (n1 n2 : nat) : nat :=
    match n1 with
    | O => O
    | S n1' => plus n2 (mult n1'  n2)
    end.
  
  Example test_mult_3_3 :
    (mult 3 3) = 9.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Fixpoint minus (n1 n2 : nat) : nat :=
    match n1, n2 with
    | O, _ => O
    | n1', O => n1'
    | S n1', S n2' => minus n1' n2'
    end.

  Example test_minus_4_2 :
    (minus 4 2) = 2.
  Proof.
    simpl.
    reflexivity.
  Qed.

  (* Notation "x + y" := (plus x y)
    (at level 50, left associativity) : nat_scope.
  Notation "x * y" := (mult x y)
    (at level 40, left associativity) : nat_scope.
  Notation "x - y" := (minus x y)
    (at level 50, left associativity) : nat_scope. *)

  Check ((0 + 1) + 1) : nat.

  Fixpoint eqb(n1 n2 : nat) : bool :=
    match n1 with
    | O =>
      match n2 with
      | O => true
      | _ => false
      end
    | S n1' =>
      match n2 with
      | O => false
      | S n2' => eqb n1' n2'
      end
    end.

  Fixpoint eqb' (n1 n2 : nat) : bool :=
    match n1, n2 with
    | O, O => true
    | O, _ => false
    | _, O => false
    | S n1', S n2' => eqb' n1' n2'
    end.

  Fixpoint leb (n1 n2 : nat) : bool :=
    match n1, n2 with
    | O, O => true
    | O, _ => true
    | _, O => false
    | S n1', S n2' => leb n1' n2'
    end.
  
  Fixpoint geb (n1 n2 : nat) : bool :=
    match n1, n2 with
    | O, O => true
    | _, O => true
    | O, _ => false
    | S n1', S n2' => geb n1' n2'
    end.
  
  Notation "x =? y" := (eqb x y)
    (at level 70) : nat_scope.
  Notation "x <=? y" := (leb x y)
    (at level 70) : nat_scope.
  Notation "x >=? y" := (geb x y)
    (at level 70) : nat_scope.
  
  Example test_leb_3_4 :
    (3 <=? 4) = true.
  Proof.
    simpl.
    reflexivity.
  Qed.

End NatNumber2.


Fixpoint eqb(n1 n2 : nat) : bool :=
  match n1 with
  | O =>
    match n2 with
    | O => true
    | _ => false
    end
  | S n1' =>
    match n2 with
    | O => false
    | S n2' => eqb n1' n2'
    end
  end.


Fixpoint leb (n1 n2 : nat) : bool :=
  match n1, n2 with
  | O, O => true
  | O, _ => true
  | _, O => false
  | S n1', S n2' => leb n1' n2'
  end.

Fixpoint geb (n1 n2 : nat) : bool :=
  match n1, n2 with
  | O, O => true
  | _, O => true
  | O, _ => false
  | S n1', S n2' => geb n1' n2'
  end.

Notation "x =? y" := (eqb x y)
  (at level 70) : nat_scope.
Notation "x <=? y" := (leb x y)
  (at level 70) : nat_scope.
Notation "x >=? y" := (geb x y)
  (at level 70) : nat_scope.


Theorem plus_O_n :
  forall (n : nat), plus O n = n.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.

Theorem plus_n_O :
  forall (n: nat), plus n O = n.
Proof.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Theorem mult_O_n :
  forall (n : nat), mult O n = O.
Proof.
  intros.
  simpl.
  reflexivity.
Qed.


Theorem mult_n_O :
  forall (n : nat), mult n O = O.
Proof.
  induction n.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHn.
    reflexivity.
Qed.

Theorem plus_id :
  forall (n m : nat), n = m -> plus n n = plus m m.
Proof.
  intros.
  rewrite <- H.
    (* rewrite -> H. *)
  reflexivity.
Qed.

Check mult_n_O.


Theorem mult_n_o_m_o :
  forall (p q : nat), (p * O) + (q * O) = O.
Proof.
  intros.
  rewrite -> mult_n_O.
  rewrite -> mult_n_O.
  simpl.
  reflexivity.
  (* induction p.
  - simpl.
    apply mult_n_O.
  - intros.
    simpl.
    rewrite IHp.
    reflexivity. *)
Qed.


Theorem plus_n_S_eqb_O :
  forall (n : nat), ((plus n (S O)) =? O) = false.
Proof.
  intros.
  destruct n as [| n'] eqn : E.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.


Theorem negb_involutive :
  forall (b : bool), negb (negb b) = b.
Proof.
  intros b.
  destruct b eqn : E.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.


Theorem andb_commutative :
  forall (a b : bool), andb a b = andb b a.
Proof.
  intros a b;
  destruct a, b;
  simpl;
  reflexivity.
Qed.


Theorem plus_1_neq_O :
  forall (n : nat), (plus n (S O)) =? O = false.
Proof.
  (* intros n. destruct n. *)
  intros [|n].
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.


Theorem andb_commutative' :
  forall (a b : bool), andb a b = andb b a.
Proof.
  intros [] [];
  simpl;
  reflexivity.
Qed.




