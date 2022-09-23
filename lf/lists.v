From LF Require Export Basics.
From LF Require Export Inductions.


Module NatList.

  Inductive natprod : Type :=
    | pair (n1 n2 : nat).


  Check (pair 3 5).

  Definition fst (p : natprod) : nat :=
    match p with
    | pair a _ => a
    end.

  Definition snd (p : natprod) : nat :=
    match p with
    | pair _ b => b
    end.

  Compute (fst (pair 2 5)).

  Notation "( x , y )" := (pair x y).

  Compute (fst (3, 5)).

  Definition swap_pair (p : natprod) : natprod :=
    match p with
    | (a, b) => (b, a)
    end.

  Theorem surjective_pair :
    forall a b : nat, (a, b) = (fst (a, b), snd (a, b)).
  Proof.
      intros.
      simpl.
      reflexivity.
  Qed.
  
  Theorem surjective_pair_stuck :
    forall p : natprod, p = (fst p, snd p).
  Proof.
    intros.
    destruct p as [p1 p2] eqn : E.
    reflexivity.
  Qed.
  
  Theorem snd_fst_is_swap :
    forall p : natprod, (snd p, fst p) = swap_pair p.
  Proof.
    intros p.
    destruct p as [p1 p2].
    simpl.
    reflexivity.
  Qed.

  Theorem fst_swap_is_snd :
    forall (p : natprod), fst (swap_pair p) = snd p.
  Proof.
    intros p.
    destruct p as [p1 p2].
    simpl.
    reflexivity.
  Qed.


  Inductive natlist : Type :=
  | nil
  | cons (n : nat) (l : natlist).
  

  Definition mylist0 := cons 1 (cons 2 (cons 3 nil)).

  Notation "x :: l" :=
    (cons x l)
    (at level 60, right associativity).
  
  Notation "[ ]" := nil.
  
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

  Definition mylist1 := 1 :: (2 :: (3 :: nil)).
  Definition mylist2 := 1 :: 2 :: 3 :: nil.
  Definition mylist3 := 1 :: 2 :: 3 :: [].
  Definition mylist4 := [1; 2; 3].
  

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
    | O => []
    | S c' => n :: repeat n c'
    end.
  
  Fixpoint length (n : natlist) : nat :=
    match n with
    | nil => O
    | _ :: n' => S (length n')
    end.

  Fixpoint append (n1 n2 : natlist) : natlist :=
    match n1 with
    | nil => n2
    | e' :: n1' => e' :: (append n1' n2)
    end.

  Notation "x ++ y" := (append x y)
    (at level 60, right associativity).
  
    
  Example test_app :
    (append [1; 2; 3] [4; 5; 6]) = [1; 2; 3; 4; 5; 6].
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_app_nil_first :
    (append nil [1; 2; 3]) = [1; 2; 3].
  Proof.
    reflexivity.
  Qed.
  
  Example test_app_nil_second :
    (append [1; 2; 3] nil) = [1; 2; 3].
  Proof.
    simpl.
    reflexivity.
  Qed.

  Definition hd (default : nat) (l : natlist) : nat :=
    match l with
    | nil => default
    | h' :: _ => h'
    end.

  Definition tl (l : natlist) : natlist :=
    match l with
    | nil => nil
    | _ :: l' => l'
    end.
  
  Fixpoint nonzeros (l : natlist) : natlist :=
    match l with
    | nil => nil
    | O :: l' => nonzeros l'
    | h' :: l' => h' :: nonzeros l'
    end.
  
  Example test_nonzeros :
    nonzeros [0;1;2;3;0;4] = [1;2;3;4].
  Proof.
    simpl.
    reflexivity.
  Qed.


  Fixpoint odd (n : nat) : bool :=
    match n with
    | O => false
    | S O => true
    | S (S n') => odd n'
    end.

  Fixpoint oddmembers (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h' :: l' =>
      if (odd h') then h' :: oddmembers l'
      else oddmembers l'
    end.
  
  Example test_oddmembers :
    oddmembers [0;1;2;3;4;5;6] = [1;3;5].
  Proof.
    simpl.
    reflexivity.
  Qed.

  Definition countoddmembers (l : natlist) : nat :=
    length (oddmembers l).
  
  Example test_countoddmembers_0 :
    countoddmembers [0;2;4;6] = 0.
  Proof.
    compute.
    reflexivity.
  Qed.

  Example test_countoddmembers_3 :
    countoddmembers [1;2;3;4;5] = 3.
  Proof.
    compute.
    reflexivity.
  Qed.

  Example test_countoddmembers_nil :
    countoddmembers nil = 0.
  Proof.
    compute.
    reflexivity.
  Qed.

  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1, l2 with
    | nil, l2' => l2'
    | l1', nil => l1'
    | h1 :: l1', h2 :: l2' => h1 :: h2 :: alternate l1' l2'
    end.
  
  Example test_alternate_same_len :
    alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_alternate_diff_len1 :
    alternate [1] [2;3;4] = [1;2;3;4].
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_alternate_diff_len2 :
    alternate [1;2;3] [4] = [1;4;2;3].
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_alternate_nil :
    alternate [1;2;3] nil = [1;2;3].
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_alternate_same_elements :
    alternate [1;2] [1;2] = [1;1;2;2].
  Proof.
    simpl.
    reflexivity.
  Qed.

  Fixpoint nat_eq (n1 n2 : nat) : bool :=
    match n1, n2 with
    | O, O => true
    | O, _ => false
    | _, O => false
    | S n1', S n2' => nat_eq n1' n2'
    end.
  
  Notation "x =? y" := (nat_eq x y)
    (at level 70).

  Definition bag := natlist.
  
  Fixpoint count (v : nat) (s : bag) : nat :=
    match s with
    | nil => O
    | h :: s' =>
      if h =? v then S (count v s')
      else count v s'
    end.
  
  Example test_count_3 :
    count 1 [1;2;3;1;4;1] = 3.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_count_0 :
    count 6 [1;2;3;1;4;1] = 0.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Definition sum (a b : bag) : bag :=
    a ++ b.
    
  Example test_sum1 :
    count 1 (sum [1;2;3] [1;4;1]) = 3.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Definition add (v : nat) (s : bag) : bag :=
    v :: s.
  
  Example test_add1 :
    count 1 (add 1 [1;4;1]) = 3.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_add2 :
    count 5 (add 1 [1;4;1]) = 0.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Fixpoint member (v : nat) (s : bag) : bool :=
    match s with
    | nil => false
    | h :: s' =>
      if h =? v then true
      else member v s'
    end.
  
  Example test_member1 :
    member 1 [1;4;1] = true.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_member2 :
    member 2 [1;4;1] = false.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Fixpoint remove_one (v : nat) (l : bag) : bag :=
    match l with
    | nil => nil
    | h :: l' =>
      if h =? v then l'
      else h :: remove_one v l'
    end.
  
  Example test_remove1 :
    count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof.
    simpl.
    reflexivity.
  Qed.


  Example test_remove_one2:
    count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_remove_one3:
    count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_remove_one4:
    count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof.
    simpl.
    reflexivity.
  Qed.
  
  Fixpoint remove_all (v : nat) (s : bag) : bag :=
    match s with
    | nil => nil
    | h :: s' =>
      if h =? v then remove_all v s'
      else h :: remove_all v s'
    end.
  
  Example test_remove_all1 :
    count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  Proof.
    simpl.
    reflexivity.
  Qed.
  
  Example test_remove_all2 :
    count 5 (remove_all 5 [2;1;4;1]) = 0.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_remove_all3 :
    count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_remove_all4 :
    count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Fixpoint included (s1 : bag) (s2 : bag) : bool :=
    match s1 with
    | nil => true
    | h :: s' =>
      if member h s2 then included s' (remove_one h s2)
      else false
    end.
  
  Example test_included1 :
    included [1;2] [2;1;4;1] = true.
  Proof.
    simpl.
    reflexivity.
  Qed.


  Example test_included2 :
    included [1;2;2] [2;1;4;1] = false.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Theorem add_inc_count :
    forall (s : bag) (v : nat),
      count v (add v s) = S (count v s).
  Proof.
  Abort.

  
  Theorem nil_app :
    forall l : natlist, [] ++ l = l.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Theorem tl_length_pred :
    forall l : natlist, pred (length l) = length (tl l).
  Proof.
    intros.
    induction l as [|l'].
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
  Qed.
  
  Theorem tl_length_pred' :
    forall l : natlist, pred (length l) = length (tl l).
  Proof.
    intros.
    destruct l as [|l'].
    - simpl.
      reflexivity.
    - simpl.
      reflexivity.
  Qed.

  Theorem app_assoc :
    forall (l1 l2 l3 : natlist), (l1 ++ l2) ++ l3 = l1 ++ (l2 ++l3).
  Proof.
    intros.
    induction l1 as [|l1'].
    - simpl.
      reflexivity.
    - simpl.
      rewrite IHl1.
      reflexivity.
  Qed.

  Fixpoint rev (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: l' => (rev l') ++ [h]
    end.

  Example test_rev1 :
    rev [1;2;3] = [3;2;1].
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_rev2 :
    rev nil = nil.
  Proof.
    reflexivity.
  Qed.

  Theorem app_len :
    forall (l1 l2 : natlist), length (l1 ++ l2) = (length l1) + (length l2).
  Proof.
    intros.
    induction l1 as [|l1'].
    - simpl.
      reflexivity.
    - simpl.
      rewrite IHl1.
      reflexivity.
  Qed.


  Theorem rev_length_firsttry :
    forall (l : natlist), length (rev l) = length l.
  Proof.
    induction l as [|n l' IHl'].
    - reflexivity.
    - simpl.
      rewrite <- IHl'.
      rewrite app_len.
      simpl.
      rewrite add_commutative.
      simpl.
      reflexivity.
  Qed.
  
  Search rev.
  Search (_ + _ = _ + _).
  Search (?x + ?y = ?y + ?x).

  Theorem app_nil_r :
    forall l : natlist, l ++ [] = l.
  Proof.
    induction l as [|l'].
    - reflexivity.
    - simpl.
      rewrite IHl.
      reflexivity.
  Qed.

  Theorem rev_app_distr :
    forall (l1 l2 : natlist), rev (l1 ++ l2) = (rev l2) ++ (rev l1).
  Proof.
    intros.
    induction l1 as [|l1'].
    - simpl.
      rewrite app_nil_r.
      reflexivity.
    - simpl.
      rewrite IHl1.
      rewrite app_assoc.
      reflexivity.
  Qed.

  Theorem rev_involution :
    forall l : natlist, rev (rev l) = l.
  Proof.
    induction l as [|l'].
    - simpl.
      reflexivity.
    - simpl.
      rewrite rev_app_distr.
      rewrite IHl.
      simpl.
      reflexivity.
  Qed.


  Theorem app_assoc4 :
    forall (l1 l2 l3 l4 : natlist),
    l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros.
    induction l1 as [|l1'].
    - simpl.
      rewrite <- app_assoc.
      reflexivity.
    - simpl.
      rewrite IHl1.
      reflexivity.
  Qed.
  
  Theorem nonzeros_app :
    forall (l1 l2 : natlist),
    nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  Proof.
    intros.
    induction l1 as [|l1'].
    - simpl.
      reflexivity.
    - destruct l1'.
      -- simpl.
         rewrite IHl1.
         reflexivity.
      -- simpl.
         rewrite IHl1.
         reflexivity. 
  Qed.
  

  Fixpoint eqblist (l1 l2 : natlist) : bool :=
    match l1, l2 with
    | nil, nil => true
    | nil, _ => false
    | _, nil => false
    | h1 :: l1', h2 :: l2' =>
        if h1 =? h2 then eqblist l1' l2'
        else false
    end.
  
  Example test_eqblist1 :
    (eqblist nil nil) = true.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_eqblist2 :
    (eqblist [1;2;3] [1;2;3]) = true.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_eqblist3 :
    eqblist [1;2;3] [1;2;4] = false.
  Proof.
    simpl.
    reflexivity.
  Qed.


  Theorem eqblist_refl :
    forall (l : natlist), true = eqblist l l.
  Proof.
    intros.
    induction l as [|l'].
    - simpl.
      reflexivity.
    - rewrite IHl.
      induction l' as [|l''].
      -- simpl.
         reflexivity.
      -- 
  Admitted.
  

  Theorem count_member_nonzero :
    forall (s : bag), 1 <=? (count 1 (1 :: s)) = true.
  Proof.
    induction s.
    - simpl.
      reflexivity.
    - destruct n.
      --
  Admitted.

  Theorem leb_n_Sn :
    forall (n : nat), n <=? (S n) = true.
  Proof.
    intros.
    induction n as [|n'].
    - simpl.
      reflexivity.
    - simpl.
      rewrite IHn'.
      reflexivity.
  Qed.
  
  
  Theorem remove_does_not_increase_count :
    forall (s : bag),
    (count 0 (remove_one 0 s)) <=? (count 0 s) = true.
  Proof.
    intros.
    induction s as [|s'].
    - simpl.
      reflexivity.
    - destruct s'.
      -- simpl.
         rewrite leb_n_Sn.
         reflexivity.
      -- simpl.
         apply IHs. 
  Qed.

  Theorem involution_injection :
    forall (f : nat -> nat),
    (forall n : nat, n = f (f n)) -> (forall n1 n2: nat, f n1 = f n2 -> n1 = n2).
  Proof.
    
  Admitted.
  
  (* ------- *)
  (* options *)
  (* ------- *)

  Fixpoint nth_bad (l : natlist) (n : nat) : nat :=
    match l with
    | nil => 42
    | a :: l' =>
      match n with
      | O => a
      | S n' => nth_bad l' n'
      end
    end.
  
  Inductive natoption : Type :=
  | None
  | Some (n : nat).

  Fixpoint nth_err (l : natlist) (n : nat) : natoption :=
    match l with
    | nil => None
    | a :: l' =>
      match n with
      | O => Some a
      | S n' => nth_err l' n'
      end
    end.
  
  Example test_nth_err1 :
    nth_err [4;5;6;7] 0 = Some 4.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_nth_err2 :
    nth_err [4;5;6;7] 3 = Some 7.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_nth_err3 :
    nth_err [4;5;6;7] 9 = None.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Definition option_elim (default : nat) (o : natoption) : nat :=
    match o with
    | None => default
    | Some v => v
    end.
  
  Definition hd_err (l: natlist) :natoption :=
    match l with
    | nil => None
    | h :: _ => Some h
    end.

  Example test_hd_err1 :
    hd_err [] = None.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_hd_err2 :
    hd_err [1] = Some 1.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Example test_hd_err3 :
    hd_err [5;6] = Some 5.
  Proof.
    simpl.
    reflexivity.
  Qed.

  Theorem option_elim_hd :
    forall (l : natlist) (default : nat),
    hd default l = option_elim default (hd_err l).
  Proof.
    intros.
    destruct l as [|l'].
    - simpl.
      reflexivity.
    - simpl.
      reflexivity. 
  Qed.


  Inductive id : Type :=
  | Id (n : nat).

  Definition eqb_id (x1 x2 : id) :=
    match x1, x2 with
    | Id x1', Id x2' => x1' =? x2'
    end.

  Theorem nat_eqb_refl :
    forall x : nat, x =? x = true.
  Proof.
    intros x.
    induction x as [| x'].
    - simpl.
      reflexivity.
    - simpl.
      rewrite IHx'.
      reflexivity.
  Qed.
  


  Theorem eqb_id_refl :
    forall x : id, eqb_id x x = true.
  Proof.
    intros.
    destruct x.
    induction n as [|n'].
    - simpl.
      reflexivity.
    - simpl.
      apply nat_eqb_refl. 
  Qed.
End NatList.



Module PartialMap.
  Export NatList.

  Inductive partial_map : Type :=
  | empty
  | record (i : id) (v : nat) (m : partial_map).


  Definition update (pm : partial_map) (x : id) (v : nat) : partial_map :=
    record x v pm.

  Fixpoint find (x : id) (pm : partial_map) : natoption :=
    match pm with
    | empty => None
    | record k v pm' =>
      if eqb_id k x then Some v
      else find x pm'
    end.
  
  Theorem eq_id_refl:
    forall x : id, eqb_id x x = true.
  Proof.
    intros.
    destruct x as [x'].
    simpl.
    apply nat_eqb_refl.
  Qed.
  
  Lemma nat_eqb_commu:
    forall (a b : nat), (a =? b) = (b =? a).
  Proof.
    induction a as [|a'].
    - destruct b as [|b'].
      -- reflexivity.
      -- simpl.
         reflexivity.
    - intros b.
      destruct b as [|b'].
      -- simpl.
         reflexivity.
      -- simpl.
         rewrite IHa'.
         reflexivity.
  Qed.
  

  Lemma eqb_id_commu :
    forall (x y : id), eqb_id x y = eqb_id y x.
  Proof.
    intros.
    destruct x. destruct y.
    simpl.
    apply nat_eqb_commu.
  Qed.
  

  Theorem update_eq :
    forall (pm : partial_map) (i : id) (v : nat),
    find i (update pm i v) = Some v.
  Proof.
    intros.
    destruct pm as [|pm'].
    - simpl.
      rewrite eq_id_refl.
      reflexivity.
    - simpl.
      rewrite eq_id_refl.
      reflexivity. 
  Qed.

  Theorem update_neq :
    forall (pm : partial_map) (x y : id) (o : nat),
    eqb_id x y = false -> find x (update pm y o) = find x pm.
  Proof.
    intros.
    destruct pm as [|pm'].
    - simpl.
      rewrite eqb_id_commu.
      rewrite H.
      reflexivity.
    - simpl.
      rewrite eqb_id_commu.
      rewrite H.
      reflexivity. 
  Qed.
  
  Inductive baz : Type :=
  | Baz1 (x : baz)
  | Baz2 (y : baz) (b : bool).

  (* How many elements does the type baz have? *)

End PartialMap.

