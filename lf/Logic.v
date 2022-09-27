From LF Require Export Tactics.


Check (3 = 3) : Prop.
Check (forall n m : nat, n + m = m + n).

Check (2 = 2) : Prop.
Check (3 = 2) : Prop.
Check (forall n : nat, n = 2) : Prop.


Theorem plus_2_2_is_4 :
  2 + 2 = 4.
Proof.
  simpl.
  reflexivity.
Qed.


Definition plus_claim : Prop := 2 + 2 = 4.

Check plus_claim : Prop.


Theorem plus_claim_is_true :
  plus_claim.
Proof.
  reflexivity.
Qed.



Definition is_three (n : nat) : Prop :=
  n = 3.

Check is_three : nat -> Prop.



Definition injective {A B} (f : A -> B) :=
  forall x y : A, f x = f y -> x = y.


Lemma succ_inj : injective S.
Proof.
  intros n m H.
  injection H as H'.
  apply H'.
Qed.


Check @eq : forall A : Type, A -> A -> Prop.


Example and_example :
  3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  split.
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.


Lemma and_intro :
  forall A B : Prop, A -> B -> A /\ B.
Proof.
  intros A B H1 H2.
  split.
  - apply H1.
  - apply H2.
Qed.



Example and_example' :
  3 + 4 = 7 /\ 2 * 2 = 4.
Proof.
  apply and_intro.
  - reflexivity.
  - reflexivity.
Qed.



Example and_exercise :
  forall n m : nat, n + m = 0 -> n = 0 /\ m = 0.
Proof.
  intros n m H.
  apply and_intro.
  - destruct n as [|n'].
    + reflexivity.
    + simpl in H.
      discriminate H.
  - destruct m as [|m'].
    + reflexivity.
    + rewrite add_commutative in H.
      simpl in H.
      discriminate H.
Qed.


Lemma and_example2 :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m H.
  destruct H as [H1 H2].
  rewrite H1.
  rewrite H2.
  simpl.
  reflexivity.
Qed.

Lemma and_example2' :
  forall n m : nat, n = 0 /\ m = 0 -> n + m = 0.
Proof.
  intros n m [H1 H2].
  rewrite H1.
  rewrite H2.
  simpl.
  reflexivity.
Qed.


Lemma and_example2'' :
  forall n m : nat, n = 0 -> m = 0 -> n + m = 0.
Proof.
  intros n m H1 H2.
  rewrite H1.
  rewrite H2.
  simpl.
  reflexivity.
Qed.

Lemma and_example3 :
  forall n m : nat, n + m = 0 -> n * m = 0.
Proof.
  intros n m H.
  apply and_exercise in H.
  destruct H as [H1 H2].
  rewrite H1.
  rewrite H2.
  simpl.
  reflexivity.
Qed.

Lemma proj1 : forall P Q : Prop,
  P /\ Q -> P.
Proof.
  intros P Q H.
  destruct H as [H1 _].
  apply H1.
Qed.


Lemma proj2 : forall P Q : Prop,
  P /\ Q -> Q.
Proof.
  intros P Q H.
  destruct H as [_ H'].
  apply H'.
Qed.


Theorem and_commut : forall P Q : Prop,
  P /\ Q -> Q /\ P.
Proof.
  intros P Q [H1 H2].
  split.
  - apply H2.
  - apply H1.
Qed.


Theorem and_assoc : forall P Q R : Prop,
  P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  (* intros P Q R [HP [HQ HR]]. *)
  destruct H as [H1 H2].
  destruct H2 as [H3 H4].
  split.
  - split.
    apply H1.
    apply H3.
  - apply H4.
Qed.


Check and : Prop -> Prop -> Prop.



Lemma factor_is_O:
  forall n m : nat, n = 0 \/ m = 0 -> n * m = 0.
Proof.
  intros n m [Hn | Hm].
  - rewrite Hn.
    simpl.
    reflexivity.
  - rewrite Hm.
    Search mult.
    Check mult_n_O.
    apply mult_n_O.
Qed.


Lemma or_intro_l : forall A B : Prop, A -> A \/ B.
Proof.
  intros A B HA.
  left.
  apply HA.
Qed.


Lemma zero_or_succ :
  forall n : nat, n = 0 \/ n = S (pred n).
Proof.
  intros n.
  destruct n as [|n'].
  - left.
    reflexivity.
  - right.
    simpl.
    reflexivity.
Qed.



Lemma mult_is_O :
  forall n m, n * m = 0 -> n = 0 \/ m = 0.
Proof.
  intros n m H.
  destruct n as [|n'].
  - left.
    reflexivity.
  - simpl in H.
    destruct m as [|m'].
    + right.
      reflexivity.
    + simpl in H.
      discriminate H.
Qed.



Theorem or_commut : forall P Q : Prop,
  P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  destruct H as [HP | HQ].
  - right. apply HP.
  - left. apply HQ.
Qed.

Module NotPlayground.
  Definition not (P : Prop) := P -> False.

  Notation "~ x" := (not x) : type_scope.

  Check not : Prop -> Prop.

End NotPlayground.


Theorem ex_falso_quodlibet : forall (P:Prop),
  False -> P.
Proof.
  intros P H.
  destruct H.
Qed.


Theorem not_implies_our_not : forall (P : Prop),
  ~ P -> (forall (Q:Prop), P -> Q).
Proof.
  unfold not.
  intros.
  destruct H.
  apply H0.
Qed.

Notation "x <> y" := (~(x = y)).

Theorem zero_not_one : 0 <> 1.
Proof.
  unfold not.
  intros H.
  discriminate H.
Qed.



Theorem not_False :
  ~ False.
Proof.
  unfold not.
  intros H.
  destruct H.
Qed.


Theorem contradiction_implies_anything :
  forall P Q : Prop, (P /\ ~P) -> Q.
Proof.
  unfold not.
  intros P Q [HP HNP].
  apply HNP in HP.
  destruct HP.
Qed.


Theorem double_neg : forall P : Prop,
  P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros HNP.
  apply HNP in H.
  destruct H.
Qed.


Theorem contrapositive : forall (P Q : Prop),
  (P -> Q) -> (~Q -> ~P).
Proof.
  unfold not.
  intros P Q HPQ HNQ.
  intros HP.
  apply HNQ in HPQ.
  - destruct HPQ.
  - apply HP.
Qed.


Theorem not_both_true_and_false : forall P : Prop,
  ~ (P /\ ~P).
Proof.
  unfold not.
  intros P [HP HPF].
  apply HPF in HP.
  destruct HP.
Qed.


Theorem de_morgan_not_or : forall (P Q : Prop),
  ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not.
  intros P Q HNPQ.
  split.
  - intros HP.
    apply HNPQ.
    left.
    apply HP.
  - intros HQ.
    apply HNPQ.
    right.
    apply HQ.
Qed.


Theorem not_true_is_false : forall b : bool,
  b <> true -> b = false.
Proof.
  unfold not.
  intros b H1.
  destruct b.
  - apply ex_falso_quodlibet.
    apply H1. reflexivity.
  - reflexivity.
Qed.

Theorem not_true_is_false' : forall b : bool,
  b <> true -> b = false.
Proof.
  unfold not.
  intros b H.
  destruct b.
  - exfalso.
    apply H.
    reflexivity.
  - reflexivity.
Qed. 


Lemma True_is_true : True.
Proof.
  apply I.
Qed.



Definition disc_fn (n : nat) : Prop :=
  match n with
  | O => True
  | S _ => False
  end.


Theorem disc_example : forall n, ~ (O = S n).
Proof.
  unfold not.
  intros n H.
  assert (H2 : disc_fn 0).
  {
    simpl.
    apply I.
  }
  rewrite H in H2.
  simpl in H2.
  apply H2.
Qed.


Module IffPlayground.
  Definition iff (P Q : Prop) :=
    (P -> Q) -> (Q -> P).
  
  Notation "P <-> Q" := (iff P Q)
    (at level 95, no associativity)
    : type_scope.

End IffPlayground.

Theorem iff_sym: 
  forall P Q : Prop, (P <-> Q) -> (Q <-> P).
Proof.
  unfold iff.
  intros P Q H.
  destruct H as [HPQ HQP].
  split.
  - apply HQP.
  - apply HPQ.
Qed.


Lemma not_true_iff_false : forall b,
  b <> true <-> b = false.
Proof.
  unfold not.
  unfold iff.
  intros b.
  split.
  - intros H.
    apply not_true_is_false.
    unfold not.
    apply H.
  - intros HBF HBT.
    rewrite HBF in HBT.
    discriminate HBT.
Qed.


Lemma apply_iff_example1:
  forall P Q R : Prop, (P <-> Q) -> (Q -> R) -> (P -> R).
Proof.
  intros P Q R Hiff H Hq.
  apply H.
  apply Hiff.
  apply Hq.
Qed.


Lemma apply_iff_example2:
  forall P Q R : Prop, (P <-> Q) -> (P -> R) -> (Q -> R).
Proof.
  intros P Q R Hiff HPR HQ.
  apply HPR.
  apply Hiff.
  apply HQ.
Qed.

Theorem or_distributes_over_and : forall P Q R : Prop,
  P \/ (Q /\ R) <-> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R.
  unfold iff.
  split.
  - intros H.
    split.
    destruct H.
    + left. apply H.
    + destruct H. right. apply H.
    + destruct H.
      * left. apply H.
      * destruct H. right. apply H0.
  - intros H.
    destruct H as [HPQ HPR].
Abort.


From Coq Require Import Setoids.Setoid.

Lemma mul_eq_0 :
  forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  unfold iff.
  intros n m.
  split.
  - intros H.
    destruct n.
    + left.
      reflexivity.
    + destruct m.
      * right.
        reflexivity.
      * simpl in H.
        discriminate H.
  - intros H.
    destruct H as [Hn | Hm].
    + rewrite Hn.
      simpl.
      reflexivity.
    + rewrite Hm.
      apply mult_n_O.
Qed.


Lemma mul_eq_0' :
  forall n m, n * m = 0 <-> n = 0 \/ m = 0.
Proof.
  split.
  - apply mult_is_O.
  - apply factor_is_O.
Qed.


Theorem or_assoc :
  forall P Q R : Prop, P \/ (Q \/ R) <-> (P \/ Q) \/ R.
Proof.
  intros P Q R.
  split.
  - intros [H | [H | H]].
    + left. left. apply H.
    + left. right. apply H.
    + right. apply H.
  - intros [[H | H] | H].
    + left. apply H.
    + right. left. apply H.
    + right. right. apply H.
Qed.


Lemma mul_eq_0_ternary :
  forall n m p, n * m * p = 0 <-> n = 0 \/ m = 0 \/ p = 0.
Proof.
  intros n m p.
  rewrite mul_eq_0.
  rewrite mul_eq_0.
  rewrite or_assoc.
  reflexivity.
Qed.


Definition Even x := exists n : nat, x = double n.


Lemma four_is_Even : Even 4.
Proof.
  unfold Even.
  exists 2.
  reflexivity.
Qed.


Theorem exists_example_2 : forall n,
  (exists m, n = 4 + m) ->
  (exists o, n = 2 + o).
Proof.
  intros n [m Hm].
  exists (2 + m).
  apply Hm.
Qed.



Theorem dist_not_exists : forall (X : Type) (P : X -> Prop),
  (forall x, P x) -> ~ (exists x, ~ P x).
Proof.
  unfold not.
  intros.
  destruct H0 as [x E].
  apply E.
  apply H.
Qed.


Theorem dist_exists_or : forall (X:Type) (P Q : X -> Prop),
  (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  - intros [Hx [HP | HQ]].
    + left.
      exists Hx.
      apply HP.
    + right.
      exists Hx.
      apply HQ.
  - intros [HP | HQ].
    destruct HP as [Hx HP'].
    + exists Hx.
      left. apply HP'.
    + destruct HQ as [Hx HQ'].
      exists Hx.
      right. apply HQ'.
Qed.


Theorem leb_plus_exists :
  forall n m, n <=? m = true -> exists x, m = n+x.
Proof.
  intros n m.
  intros H.
  induction n as [|n'].
  - simpl.
    exists m.
    reflexivity.
  - simpl.
    destruct m.
    discriminate H.
Abort.


Lemma eq_nn : 
  forall n : nat, (n <=? n) = true.
Proof.
  intros n.
  induction n as [|n'].
  - simpl.
    reflexivity.
  - simpl.
    apply IHn'.
Qed.


Lemma leq_plus :
  forall n x : nat, (n <=? n + x) = true.
Proof.
  intros n x.
  induction x as [|x'].
  - rewrite add_commutative.
    simpl.
    apply eq_nn.
  - rewrite add_commutative.
    induction n as [|n'].
    + simpl.
      reflexivity.
    + simpl.
      rewrite add_commutative.
      simpl.
      simpl in IHn'.
      rewrite add_commutative.
      apply IHn'.
      simpl in IHx'.
      apply IHx'.
Qed.


Theorem plus_exists_leb :
  forall n m, (exists x, m = n + x) -> n <=? m = true.
Proof.
  intros n m H.
  destruct H as [Hx HE].
  rewrite HE.
  apply leq_plus.
Qed.


Fixpoint In {X : Type} (x : X) (l : list X) : Prop :=
  match l with
  | [] => False
  | h :: tl => (h = x) \/ (In x tl)
  end.

Example In_example_1 : In 4 [1;2;3;4;5].
Proof.
  simpl.
  right.
  right.
  right.
  left.
  reflexivity.
Qed.

Example In_example_2 :
  forall n, In n [2; 4] ->
  exists n', n = 2 * n'.
Proof.
  intros n H.
  simpl in H.
  destruct H as [H | [H | []]].
  - exists 1.
    rewrite <- H.
    reflexivity.
  - rewrite <- H.
    exists 2.
    reflexivity.
Qed.


Theorem In_map :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l -> In (f x) (map f l).
Proof.
  intros A B f l x H.
  induction l as [|x' l' IHl'].
  - simpl.
    simpl in H.
    apply H.
  - simpl.
    simpl in H.
    destruct H as [H1 | H2].
    + rewrite H1.
      left.
      reflexivity.
    + right.
      apply IHl'.
      apply H2.
Qed.


Theorem In_map' :
  forall (A B : Type) (f : A -> B) (l : list A) (x : A),
         In x l -> In (f x) (map f l).
Proof.
  intros A B f l x.
  induction l as [|x' l' IHl'].
  - simpl.
    intros [].
  - simpl.
    intros [H | H].
    + rewrite H.
      left.
      reflexivity.
    + right.
      apply IHl'.
      apply H.
Qed.


Theorem In_map_iff :
  forall (A B : Type) (f : A -> B) (l : list A) (y : B),
         In y (map f l) <->
         exists x, f x = y /\ In x l.
Proof.
  intros A B f l y.
  split.
  - intros H.
    induction l as [|x' l' IHl'].
    + simpl in H.
      destruct H.
    + exists x'.
      simpl in H.
      destruct H as [H | H].
      * split.
        ** apply H.
        ** simpl.
           left.
           reflexivity.
      * split.
Admitted.
       

Theorem In_app_iff : forall A l l' (a:A),
  In a (l++l') <-> In a l \/ In a l'.
Proof.
  intros A l l' a.
  split.
  - intros H.
    induction l.
    + simpl.
      simpl in H.
      right.
      apply H.
    + simpl in H.
      destruct H as [H|H].
      * simpl.
        left.
        left.
        apply H.
Abort.


Fixpoint All {T : Type} (P : T -> Prop) (l : list T) : Prop :=
  match l with
  | [] => True
  | h :: tl => (P h) /\ (All P tl)
  end.

Theorem All_In :
  forall T (P : T -> Prop) (l : list T),
    (forall x, In x l -> P x) <->
    All P l.
Proof.
  intros T P l.
  split.
  - intros H.
    induction l as [|x' l'].
    + simpl.
      apply I.
    + simpl.
      split.
      * apply H.
        simpl.
        left.
        reflexivity.
      * apply IHl'.
        intros x Hx.
        apply H.
        simpl.
        right.
        apply Hx.
  - intros H x.
    induction l as [|x' l'].
    + simpl.
      intros H'.
      destruct H'.
    + intros H'.
      apply IHl'.
      * simpl in H.
        destruct H.
        apply H0.
      * simpl in H.
        simpl in H'.
        destruct H.
        destruct H'.
        rewrite H1 in H.
        apply IHl' in H0.
Abort.


Definition combine_odd_even (Podd Peven : nat -> Prop)
                            : nat -> Prop :=
  fun x => 
    if odd x then Podd x
    else Peven x.

Theorem combine_odd_even_intro :
  forall (Podd Peven : nat -> Prop) (n : nat),
    (odd n = true -> Podd n) ->
    (odd n = false -> Peven n) ->
    combine_odd_even Podd Peven n.
Proof.
  intros Podd Peven n H1 H2.
  induction n as [|n'].
  - unfold combine_odd_even.
    simpl.
    simpl in H2.
    apply H2.
    reflexivity.
  - unfold combine_odd_even.
    + destruct (odd (S n')) eqn : EQ1.
      * apply H1.
        reflexivity.
      * apply H2.
        reflexivity.
Qed.


Theorem combine_odd_even_elim_odd :
  forall (Podd Peven : nat -> Prop) (n : nat),
    combine_odd_even Podd Peven n ->
    odd n = true ->
    Podd n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1.
  rewrite H2 in H1.
  apply H1.
Qed.


Theorem combine_odd_even_elim_even :
  forall (Podd Peven : nat -> Prop) (n : nat),
  combine_odd_even Podd Peven n ->
  odd n = false ->
  Peven n.
Proof.
  intros Podd Peven n H1 H2.
  unfold combine_odd_even in H1.
  rewrite H2 in H1.
  apply H1.
Qed.


Check plus : nat -> nat -> nat.
Check add_commutative : forall n m : nat, n + m = m + n.


Lemma add_comm3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_commutative.
  assert (H : y + z = z + y).
  {
    rewrite add_commutative.
    reflexivity.     
  }
  rewrite H.
  reflexivity.
Qed.


Lemma add_comm3_take3 :
  forall x y z, x + (y + z) = (z + y) + x.
Proof.
  intros x y z.
  rewrite add_commutative.
  rewrite (add_commutative y z).
  reflexivity.
Qed.



Theorem in_not_nil :
  forall A (x : A) (l : list A), In x l -> l <> [].
Proof.
  intros A x l H.
  unfold not.
  intros H'.
  rewrite H' in H.
  simpl in H.
  destruct H.
Qed.

Lemma in_not_nil_42 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil with (x := 42).
  apply H.
Qed.


Lemma in_not_nil_42_take3 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply in_not_nil in H.
  apply H.
Qed.


Lemma in_not_nil_42_take4 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  apply (in_not_nil nat 42).
  apply H.
Qed.

Lemma in_not_nil_42_take5 :
  forall l : list nat, In 42 l -> l <> [].
Proof.
  intros l H.
  Check in_not_nil.
  apply (in_not_nil _ _ _ H).
Qed.


Example lemma_application_ex :
  forall {n : nat} {ns : list nat},
    In n (map (fun m => m * 0) ns) ->
    n = 0.
Proof.
  intros n ns H.
  Check proj1.
  Check In_map_iff.
  destruct (proj1 _ _ (In_map_iff _ _ _ _ _) H)
    as [m [Hm _]].
  rewrite mult_commu in Hm.
  simpl in Hm.
  rewrite <- Hm.
  reflexivity.
Qed.


Example function_equality_ex1 :
  (fun x => 3 + x) = (fun x => (pred 4) + x).
Proof.
  simpl.
  reflexivity.
Qed.


Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  simpl.
Abort.


Axiom functional_extensionality :
  forall {X Y: Type} {f g : X -> Y},
  (forall (x : X), f x = g x) -> f = g.


Example function_equality_ex2 :
  (fun x => plus x 1) = (fun x => plus 1 x).
Proof.
  apply functional_extensionality.
  intros x.
  simpl.
  rewrite add_commutative.
  simpl.
  reflexivity.
Qed.


Print Assumptions function_equality_ex2.


(* tail-recursive *)

Fixpoint rev_append {X} (l1 l2 : list X) : list X :=
  match l1 with
  | [] => l2
  | x :: l1' => rev_append l1' (x :: l2)
  end.


Definition tr_rev {X} (l : list X) : list X :=
  rev_append l [].


Lemma app_empty :
  forall (X : Type) (l : list X),
  l ++ [] = l.
Proof.
  intros X l.
  induction l.
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity. 
Qed.



Lemma rev_app_app:
  forall (X : Type) (l1 l2 : list X),
  rev_append l1 l2 = (rev_append l1 []) ++ l2.
Proof.
  intros X l1.
  induction l1 as [|x' l1'].
  - intros l2.
    simpl.
    reflexivity.
  - intros l2.
    simpl.
    rewrite IHl1'.
    simpl.
Admitted.



Theorem tr_rev_correct : forall X, @tr_rev X = @rev X.
Proof.
  intros X.
  apply functional_extensionality.
  intros l.
  unfold tr_rev.
  induction l as [|x' l'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite <- IHl'.
    apply rev_app_app.
Qed.
    
    
Example even_42_bool : even 42 = true.
Proof.
  simpl.
  reflexivity.
Qed.


Example even_42_prop : Even 42.
Proof.
  unfold Even.
  exists 21.
  simpl.
  reflexivity.
Qed.


Lemma even_double : forall k, even (double k) = true.
Proof.
  intros k.
  induction k.
  - simpl.
    reflexivity.
  - simpl.
    apply IHk.
Qed.

Lemma even_double_conv : forall n, exists k,
  n = if even n then double k else S (double k).
Proof.
  intros n.
  induction n as [|n'].
  - simpl.
    exists 0.
    simpl.
    reflexivity.
Admitted.


Theorem even_bool_prop : forall n,
  even n = true <-> Even n.
Proof.
  intros n.
  split.
  - intros H.
    destruct (even_double_conv n) as [k Hk].
    rewrite H in Hk.
    rewrite Hk.
    unfold Even.
    exists k.
    reflexivity.
    Check Even.
  - intros [k Hk].
    rewrite Hk.
    apply even_double.
Qed.



Theorem eqb_eq : forall n1 n2 : nat,
  n1 =? n2 = true <-> n1 = n2.
Proof.
  intros n1 n2.
  split.
  - intros H.
    Check eqb_true.
    apply (eqb_true n1 n2) in H.
    apply H.
  - intros H.
    rewrite H.
    assert (Heq : forall n : nat, (n=?n) = true).
    {
      intros n.
      induction n.
      - simpl.
        reflexivity.
      - simpl.
        apply IHn.
    }
    apply Heq.
Qed.




        


  





  

