From LF Require Export Poly.

Theorem silly1 :
  forall (n m : nat), n = m -> n = m.
Proof.
    intros n m eq.
    apply eq.
Qed.


Theorem silly2 :
  forall (n m o p : nat),
  n = m -> (n = m -> [n;o] = [m;p]) -> [n;o] = [m;p].
Proof.
  intros n m o p eq1 eq2.
  apply eq2.
  apply eq1.
Qed.


Theorem silly2a : 
  forall (n m : nat), (n, n)= (m, m) ->
    (forall (q r : nat), (q, q) = (r, r) -> [q] = [r]) ->
      [n] = [m].
Proof.
  intros n m eq1 eq2.
  apply eq2.
  apply eq1.
Qed.


Theorem silly_ex : forall p,
  (forall n, even n = true -> even (S n) = false) ->
  (forall n, even n = false -> odd n = true) ->
  even p = true ->
  odd (S p) = true.
Proof.
  intros p eq1 eq2 eq3.
  apply eq2.
  apply eq1.
  apply eq3.
Qed.


Theorem silly3 : forall (n m : nat),
  n = m -> m = n.
Proof.
  intros n m eq1.
  symmetry.
  apply eq1.
Qed.


Theorem rev_exercise1 : forall (l l' : list nat),
  l = rev l' ->
  l' = rev l.
Proof.
  intros l l' H.
  rewrite H.
  Search rev.
  symmetry.
  apply rev_involution.
Qed.


Example trans_eq_example : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.


Theorem trans_eq : forall (X : Type) (n m o : X),
  n = m -> m = o -> n = o.
Proof.
  intros X n m o H1 H2.
  rewrite H1.
  apply H2.
Qed.


Example trans_eq_example' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f H1 H2.
  (*
  If we simply tell Coq apply trans_eq at this point,
  it can tell (by matching the goal against the conclusion
  of the lemma) that it should instantiate X with [nat],
  n with [a,b], and o with [e,f]. However, the matching
  process doesn't determine an instantiation for m: we
  have to supply one explicitly by adding "with (m:=[c,d])"
  to the invocation of apply. 
  *)
  apply trans_eq with (m:=[c;d]).
  - apply H1.
  - apply H2.
Qed.


Example trans_eq_example'' : forall (a b c d e f : nat),
     [a;b] = [c;d] ->
     [c;d] = [e;f] ->
     [a;b] = [e;f].
Proof.
  intros a b c d e f H1 H2.
  transitivity [c;d].
  - apply H1.
  - apply H2.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
     m = (minustwo o) ->
     (n + p) = m ->
     (n + p) = (minustwo o).
Proof.
  intros n m o p H1 H2.
  transitivity m.
  - apply H2.
  - apply H1.
Qed.


Theorem S_injective : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  assert (H2 : n = pred (S n)).
  {
    simpl.
    reflexivity.
  }
  rewrite H2.
  rewrite H1.
  simpl.
  reflexivity.
Qed.


(*
- The constructor S is injective (or one-to-one). That is,
  if S n = S m, it must be that n = m.
- The constructors O and S are disjoint. That is, O is not
  equal to S n for any n.
*)


Theorem S_injective' : forall (n m : nat),
  S n = S m ->
  n = m.
Proof.
  intros n m H1.
  injection H1 as Hnm.
  apply Hnm.
Qed.


Theorem injection_ex1 : forall (n m o : nat),
  [n;m] = [o;o] ->
  n = m.
Proof.
  intros n m o H1.
  injection H1 as H1' H1''.
  rewrite H1'.
  rewrite H1''.
  reflexivity.
Qed.


Example injection_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = z :: j ->
    j = z :: l ->
    x = y.
Proof.
  intros X x y z l j H1 H2.
  assert (H : x :: y :: l = z :: z :: l).
  {
    rewrite H1.
    rewrite H2.
    reflexivity.
  }
  injection H as H' H''.
  rewrite H'.
  rewrite H''.
  reflexivity.
Qed.


Theorem discriminate_ex1 : forall (n m : nat),
  false = true ->
  n = m.
Proof.
  intros n m H.
  discriminate H.
Qed.


Theorem discriminate_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n H.
  discriminate H.
Qed.


Example discriminate_ex3 :
  forall (X : Type) (x y z : X) (l j : list X),
    x :: y :: l = [] ->
    x = z.
Proof.
  intros X x y z l j H1.
  discriminate H1.
Qed.


Theorem eqb_0_l : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n H1.
  destruct n as [|n'].
  - reflexivity.
  - discriminate H1.
Qed.


Theorem eqb_0_l' : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n.
  destruct n as [|n'].
  - simpl.
    intros H.
    reflexivity.
  - simpl.
    intros H.
    discriminate H.
Qed.


Theorem eqb_0_l'' : forall n,
   0 =? n = true -> n = 0.
Proof.
  intros n H1.
  destruct n as [|n'].
  - reflexivity.
  - assert (H : forall x : nat, 0 =? S x = false).
    {
      intros x.
      simpl.
      reflexivity.
    }
    assert (H' : true = false).
    {
      rewrite <- H1.
      rewrite -> H.
      reflexivity.
    }
    discriminate H'.
Qed.


Theorem f_equal :
  forall (A B : Type) (f: A -> B) (x y: A),
    x = y -> f x = f y.
Proof.
  intros A B f x y H1.
  rewrite H1.
  reflexivity.
Qed.


Theorem eq_implies_succ_equal :
  forall (n m : nat),
    n = m -> S n = S m.
Proof.
  intros n m H1.
  apply f_equal.
  apply H1.
Qed.


Theorem eq_implies_succ_equal' :
  forall (n m : nat),
    n = m -> S n = S m.
Proof.
  intros n m H1.
  f_equal.
  apply H1.
Qed.


Theorem S_inj : forall (n m : nat) (b : bool),
  ((S n) =? (S m)) = b ->
  (n =? m) = b.
Proof.
  intros n m b H1.
  simpl in H1.
  apply H1.
Qed.

(* 
- Similarly, apply L in H matches some conditional statement L
  (of the form X → Y, say) against a hypothesis H in the
  context. However, unlike ordinary apply (which rewrites a
  goal matching Y into a subgoal X), apply L in H matches H
  against X and, if successful, replaces it with Y.
- In other words, apply L in H gives us a form of "forward
  reasoning": given X → Y and a hypothesis matching X, it
  produces a hypothesis matching Y.
- By contrast, apply L is "backward reasoning": it says that
  if we know X → Y and we are trying to prove Y, it suffices
  to prove X. 
*)

Theorem silly4 : forall (n m p q : nat),
  (n = m -> p = q) ->
  m = n ->
  q = p.
Proof.
  intros n m p q H1 H2.
  symmetry in H2.
  apply H1 in H2.
  symmetry.
  apply H2.
Qed.

(* 
  Forward reasoning starts from what is given (premises,
  previously proven theorems) and iteratively draws
  conclusions from them until the goal is reached. Backward
  reasoning starts from the goal and iteratively reasons
  about what would imply the goal, until premises or previously
  proven theorems are reached. 
*)


Fixpoint double (n : nat) : nat :=
  match n with
  | O => O
  | S n' => S (S (double n'))
  end.

Theorem double_injective_FAILED :
  forall n m, double n = double m -> n = m.
Proof.
  intros n m.
  induction n as [|n' IHn'].
  - simpl.
    intros eq.
    destruct m as [|m'].
    -- reflexivity.
    -- discriminate eq.
  - intros eq.
    destruct m as [|m'].
    discriminate eq.
    f_equal.
Abort.


Theorem double_injective : forall n m,
  double n = double m ->
  n = m.
Proof.
  intros n.
  induction n as [|n' IHn'].
  - intros m H.
    destruct m.
    -- reflexivity.
    -- discriminate H.
  - intros m H.
    destruct m as [|m'].
    -- discriminate H.
    -- apply f_equal.
      apply IHn'.
      simpl in H.
      injection H as goal.
      apply goal.
Qed.


(* 
  The thing to take away from all this is that you need to
  be careful, when using induction, that you are not trying
  to prove something too specific: When proving a property
  involving two variables n and m by induction on n, it is
  sometimes crucial to leave m generic.
*)


Theorem eqb_true :
  forall n m, n =? m = true -> n = m.
Proof.
  intros n.
  induction n.
  - intros m H.
    destruct m as [|m'].
    -- reflexivity.
    -- discriminate H.
  - intros m H.
    destruct m as [|m'].
    -- discriminate H.
    -- simpl in H.
       assert (Ha : forall (a b : nat), a = b -> S a = S b).
       {
          intros a b Ha'.
          rewrite Ha'.
          reflexivity.
       }
       apply Ha.
       apply (IHn m').
       apply H.
Qed.



Theorem plus_n_n_injective :
  forall n m, n + n = m + m -> n = m.
Proof.
  intros n.
  induction n as [|n'].
  - intros m H.
    destruct m as [|m'].
    -- reflexivity.
    -- discriminate H.
  - intros m H.
    destruct m as [|m'].
    -- discriminate H.
    -- f_equal.
       apply IHn'.
       simpl in H.
       rewrite <- add_m_Sn in H.
       rewrite <- add_m_Sn in H.
       injection H as H'.
       apply H'.
Qed.


Lemma plus_SSab:
  forall (a b : nat), S a + S b = S (S (a + b)).
Proof.
  intros a.
  induction a as [|a'].
  - simpl.
    reflexivity.
  - intros b.
    simpl.
    simpl in IHa'.
    rewrite -> IHa'.
    reflexivity.  
Qed.


Theorem plus_n_n_injective' :
  forall n m, n + n = m + m -> n = m.
Proof.
  intros n.
  induction n as [|n'].
  - intros m H.
    destruct m as [|m'].
    -- reflexivity.
    -- discriminate H.
  - intros m H.
    destruct m as [|m'].
    -- discriminate H.
    -- f_equal.
       apply IHn'.
       rewrite plus_SSab in H.
       rewrite plus_SSab in H.
       injection H as H'.
       apply H'.
Qed.


Theorem double_injective_take2 :
  forall n m, double n = double m -> n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|m'].
  - simpl.
    intros n H.
    destruct n as [|n'].
    -- reflexivity.
    -- discriminate H.
  - simpl.
    intros n H.
    destruct n as [|n'].
    -- discriminate H.
    -- f_equal.
       simpl in H.
       injection H as H'.
       apply IHm' in H'.
       apply H'.
Qed.


Theorem nth_error_after_last:
  forall (n : nat) (X : Type) (l : list X),
    length l = n -> nth_err l n = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [|l'].
  - intros n H.
    rewrite <- H.
    simpl.
    reflexivity.
  - intros n H.
    destruct n as [|n'].
    -- simpl.
       discriminate H.
    -- simpl.
       apply IHl.
       simpl in H.
       injection H as H'.
       apply H'.
Qed.


Definition square n := n * n.


Theorem mult_commu:
  forall (n m : nat), n * m = m * n.
Proof.
  intros n.
  induction n as [| n'].
  - simpl.
    induction m as [|m'].
    -- reflexivity.
    -- simpl.
       apply IHm'.
  - intros m.
    induction m as [|m'].
    -- simpl.
       rewrite IHn'.
       simpl.
       reflexivity.
    -- simpl.
       f_equal.
       rewrite IHn'.
       simpl.
       symmetry.
       rewrite <- IHm'.
       simpl.
       rewrite <- plus_assoc.  
       rewrite <- plus_assoc.
       rewrite IHn'.
       rewrite (add_commutative n' m').
       reflexivity.
Qed.


Lemma mult_plus_distr:
  forall (n m o : nat), (n + m) * o = n * o + m * o.
Proof.
  intros n.
  induction n.
  - intros m o.
    simpl.
    reflexivity.
  - intros m o.
    simpl.
    rewrite IHn. 
    rewrite <- plus_assoc.
    reflexivity.
Qed.



Lemma mult_assoc :
  forall (n m o : nat), n * m * o = n * (m * o).
Proof.
  intros n.
  induction n as [|n'].
  - intros m o.
    simpl.
    reflexivity.
  - intros m o.
    simpl.
    rewrite mult_plus_distr.
    rewrite IHn'.
    reflexivity.  
Qed.


Lemma square_mult :
  forall n m, square (n * m) = square n * square m.
Proof.
  intros n m.
  unfold square.
  rewrite <- mult_assoc.
  rewrite <- mult_assoc.
  assert (H : n * m * n = n * n * m).
  {
    rewrite mult_commu.
    rewrite mult_assoc.
    reflexivity.
  }
  rewrite H.
  reflexivity.
Qed.


Definition foo (x: nat) := 5.


Definition bar x :=
  match x with
  | O => 5
  | S _ => 5
  end.


Fact silly_fact_2_FAILED :
  forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  simpl.
Abort.


Fact silly_fact_2 :
  forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
    intros m.
    destruct m eqn:E.
    - simpl. reflexivity.
    - simpl. reflexivity.
Qed.


Fact silly_fact_2' :
  forall m, bar m + 1 = bar (m + 1) + 1.
Proof.
  intros m.
  unfold bar.
  destruct m as [|m'].
  - simpl.
    reflexivity.
  - simpl.
    reflexivity.
Qed.


Definition sillyfun (n : nat) : bool :=
  if n =? 3 then false
  else if n =? 5 then false
  else false.


Theorem sillyfun_false :
  forall (n : nat), sillyfun n = false.
Proof.
  intros n.
  unfold sillyfun.
  destruct (n =? 3) eqn: E1.
  - reflexivity.
  - destruct (n =? 5).
    -- reflexivity.
    -- reflexivity.
Qed.


(*
  In general, the destruct tactic can be used to perform case
  analysis of the results of arbitrary computations. If e is
  an expression whose type is some inductively defined type T,
  then, for each constructor c of T, destruct e generates a
  subgoal in which all occurrences of e (in the goal and in the
  context) are replaced by c.
*)

Fixpoint split1 {X Y : Type} (l : list (X * Y))
              : (list X) * (list Y) :=
  match l with
  | [] => ([], [])
  | (x, y) :: t =>
    match split1 t with
    | (lx, ly) => (x :: lx, y :: ly)
    end
  end.

Lemma eq_split_eq:
  forall (X Y : Type) (l1 l2 : list (X * Y)),
  l1 = l2 -> split1 l1 = split1 l2.
Proof.
  intros X Y l1 h2 H.
  rewrite H.
  reflexivity.
Qed.


Lemma split_eq:
  forall (X Y : Type) (l1 l2 : list (X * Y)),
  split1 l1 = split1 l2 -> l1 = l2.
Proof.
  intros X Y l1.
  induction l1.
  - intros l2 H.
    

Admitted.



Theorem combine_split :
  forall X Y (l : list (X * Y)) l1 l2,
  split l = (l1, l2) -> combine l1 l2 = l.
Proof.
  intros X Y l.
  induction l as [|l'].
  intros l1 l2 H.
  - destruct l1 as [|l1']. destruct l2 as [|l2'].
    -- simpl.
       reflexivity.
    -- simpl.
       reflexivity.
    -- destruct l2 as [|l2'].
       + simpl.
         reflexivity.
       + simpl.
         discriminate H.
  - intros l1 l2 H.
    destruct l1 as [|l1']. destruct l2 as [|l2'].
    -- simpl.
       assert (Hs : @split X Y [] = ([ ], [ ])).
       {
          simpl.
          reflexivity.
       }
       rewrite <- Hs in H.
Admitted.


Definition sillyfun1 (n : nat) : bool :=
  if n =? 3 then true
  else if n =? 5 then true
  else false.


Theorem sillyfun1_odd_FAILED :
  forall (n : nat), sillyfun1 n = true -> odd n = true.
Proof.
  intros n H.
  unfold sillyfun1 in H.
  destruct n as [|n'].
  - simpl in H.
    discriminate H.
  - simpl.
    destruct (S n' =? 3).
Abort.


Theorem sillyfun1_odd :
  forall (n : nat),
    sillyfun1 n = true -> odd n = true.
Proof.
  intros n H.
  unfold sillyfun1 in H.
  destruct (n =? 3) eqn: Heq3.
  Check eqb_true.
  - apply eqb_true in Heq3.
    rewrite Heq3.
    simpl.
    reflexivity.
  - destruct (n =? 5) eqn: Heq5.
    -- apply eqb_true in Heq5.
       rewrite Heq5.
       simpl.
       reflexivity.
    -- discriminate H.
Qed. 



Theorem bool_fn_applied_thrice :
  forall (f : bool -> bool) (b : bool),
  f (f (f b)) = f b.
Proof.
  intros f b.
  destruct (f b) eqn : F1.
Abort.


Theorem eqb_sym : forall (n m : nat),
  (n =? m) = (m =? n).
Proof.
  intros n.
  induction n as [|n'].
  - intros m.
    destruct m as [|m'].
    -- simpl.
       reflexivity.
    -- simpl.
       reflexivity.
  - intros m.
    destruct m as [|m'].
    -- simpl.
       reflexivity.
    -- simpl.
      rewrite IHn'.
      reflexivity.
Qed.   


Theorem eqb_trans : forall n m p,
  n =? m = true ->
  m =? p = true ->
  n =? p = true.
Proof.
  intros n m p H1 H2.
  destruct (n =? m) eqn: F1.
  apply eqb_true in F1.
  rewrite F1.
  - apply H2.
  - discriminate H1.
Qed.


Definition split_combine_statement : Prop :=
  forall (X Y : Type) (l1 : list X) (l2 : list Y) (l : list (X * Y)),
    combine l1 l2 = l -> split1 l = (l1, l2).


Theorem split_combine : split_combine_statement.
Proof.
Abort.


Theorem filter_exercise :
  forall (X : Type) (test : X -> bool) (x : X) (l lf : list X),
    filter test l = x :: lf -> test x = true.
Proof.
  intros X test x l lf H.
Abort.


Fixpoint forallb {X : Type} (test : X -> bool) (l : list X) :=
  match l with
  | [] => true
  | h :: tl =>
    match test h with
    | true => forallb test tl
    | false => false
    end
  end.

Fixpoint existsb {X : Type} (test : X -> bool) (l : list X) :=
  match l with
  | [] => false
  | h :: tl =>
    match test h with
    | true => true
    | false => existsb test tl
    end
  end.

Example test_forallb_1 : forallb odd [1;3;5;7;9] = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_forallb_2 : forallb negb [false;false] = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_forallb_3 : forallb even [0;2;4;5] = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_forallb_4 : forallb (eqb 5) [] = true.
Proof.
  simpl.
  reflexivity.
Qed.


Example test_existsb_1 : existsb (eqb 5) [0;2;3;6] = false.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_existsb_2 : existsb (andb true) [true;true;false] = true.
Proof.
  simpl.
  reflexivity.
Qed.


Example test_existsb_3 : existsb odd [1;0;0;0;0;3] = true.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_existsb_4 : existsb even [] = false.
Proof.
  simpl.
  reflexivity.
Qed.


Definition existsb' {X : Type} (test : X -> bool) (l : list X) : bool :=
  negb (forallb (fun x => negb (test x)) l).


Theorem existsb_existsb' : 
  forall (X : Type) (test : X -> bool) (l : list X),
    existsb test l = existsb' test l.
Proof.
  intros X test l.
  induction l as [|l'].
  - simpl.
    compute.
    reflexivity.
  - destruct (test l') eqn: T1.
    + compute.
      rewrite T1.
      reflexivity.
    + simpl.
      rewrite T1.
      symmetry.
      rewrite IHl.
Abort.

    


