From LF Require Export Lists.


Inductive list (X : Type) : Type :=
  | nil
  | cons (x : X) (l : list X).


Check list : Type -> Type.

Check (nil nat) : list nat.

Check (cons nat 3 (nil nat)) : list nat.

Check nil : forall X : Type, list X.
Check cons : forall X : Type, X -> list X -> list X. 


Check (cons nat 2 (cons nat 1 (nil nat))) : list nat.


Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat X x count')
  end.


Example test_repeat1 :
  repeat bool false 1 = cons bool false (nil bool).
Proof.
  simpl.
  reflexivity.
Qed.

Example test_repeat2 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof.
  simpl.
  reflexivity.
Qed.


Module NumberGrumble.
  Inductive number : Type :=
  | a
  | b (x : number) (y : nat)
  | c.

  Inductive grumble (X : Type) :=
  | d (m : number)
  | e (x : X).

  (* 
  Which of the following are well-typed elements of grumble X
  for some type X? (Add YES or NO to each line.)

    d (b a 5)           NO
    d mumble (b a 5)    YES
    d bool (b a 5)      YES
    e bool true         YES
    e mumble (b c 0)    YES
    e bool (b c 0)      No
    c                   NO
 *)

  Check d number (b a 5) : grumble number.
  Check d bool (b a 5) : grumble bool.
  Check e bool true : grumble bool.
  Check e number (b c 0) : grumble number.

End NumberGrumble.


Fixpoint repeat' X x count : list X :=
  match count with
  | O => nil X
  | S count' => cons X x (repeat' X x count')
  end.

Check repeat' : forall X : Type, X -> nat -> list X.
Check repeat : forall X : Type, X -> nat -> list X.


(* 
This may sound similar to type annotation inference -- and, indeed, the two procedures rely on the same underlying mechanisms. Instead of simply omitting the types of some arguments to a function, like
    repeat' X x count : list X :=
we can also replace the types with holes
    repeat' (X : _) (x : _) (count : _) : list X :=
to tell Coq to attempt to infer the missing information.
*)

Fixpoint repeat'' X x count : list X :=
  match count with
  | O => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.


Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).
Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).


(* 
The Arguments directive specifies the name of the function
(or constructor) and then lists the (leading) argument names
to be treated as implicit, each surrounded by curly braces.
*)

Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).


Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | O => nil
  | S count' => cons x (repeat''' x count')
  end.

(* 
We will use the latter style whenever possible, but __we will
continue to use explicit Argument declarations for Inductive
constructors.__ The reason for this is that marking the parameter
of an inductive type as implicit causes it to become implicit
for the type itself, not just for its constructors. For instance,
consider the following alternative definition of the list type:
*)

Inductive list' {X : Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').


Fixpoint app {X : Type} (l1 l2 : list X) : list X :=
  match l1 with
  | nil => l2
  | cons e' l1' => cons e' (app l1' l2)
  end.


Fixpoint rev {X : Type} (l : list X) : list X :=
  match l with
  | nil => nil
  | cons h tl => app (rev tl) (cons h nil)
  end.


Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => O
  | cons h tl => S (length tl)
  end.


Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = cons 2 (cons 1 nil).
Proof.
  simpl.
  reflexivity.
Qed.


Example test_rev2 :
  rev (cons true nil) = (cons true nil).
Proof.
  simpl.
  reflexivity.
Qed.


Example test_length1 :
  length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof.
  simpl.
  reflexivity.
Qed.


Fail Definition mynil := nil.

Definition mynil : list nat := nil.

Check @nil : forall (X : Type), list X.

Definition mylist' := @nil nat.


Notation "x :: y" :=
  (cons x y)
  (at level 60, right associativity).

Notation "[ ]" := nil.

Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) .. ).

Notation "x ++ y" :=
  (app x y)
  (at level 60, right associativity).

Definition list123''' := [1;2;3].

Fail Definition mynil'' := [].
Definition mynil'' : list nat := [].


Theorem app_nil_r:
  forall (X : Type), forall (l : list X), l ++ [] = l.
Proof.
  intros.
  induction l as [|l'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl.
    reflexivity.
Qed.


Theorem app_assoc :
  forall (X : Type), forall (l1 l2 l3: list X),
  app (app l1 l2) l3 = app l1 (app l2 l3).
Proof.
  intros.
  induction l1 as [|l1'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl1.
    reflexivity.
Qed.


Theorem app_length :
  forall (X : Type), forall (l1 l2 : list X),
  length (app l1 l2) = (length l1) + (length l2).
Proof.
  intros.
  induction l1 as [|l1'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl1.
    reflexivity. 
Qed.


Theorem rev_app_distr :
  forall (X : Type), forall (l1 l2 : list X),
  rev (app l1 l2) = app (rev l2) (rev l1).
Proof.
  intros.
  induction l1 as [| l1'].
  - simpl.
    rewrite app_nil_r.
    reflexivity.
  - simpl.
    rewrite IHl1.
    rewrite app_assoc.
    reflexivity. 
Qed.


Theorem rev_involution :
  forall (X : Type), forall (l : list X),
  rev (rev l) = l.
Proof.
  intros.
  induction l as [| l'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite rev_app_distr.
    rewrite IHl.
    simpl.
    reflexivity.
Qed.


Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).


Arguments pair {X} {Y}.


Notation "( x , y )" := (pair x y).


Notation "X * Y" := (prod X Y) : type_scope.

(* 
  The annotation : type_scope tells Coq that this abbreviation
  should only be used when parsing types, not when parsing
  expressions. This avoids a clash with the multiplication
  symbol.
*)


Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.


Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.


Fixpoint combine {X Y : Type} (l1 : list X) (l2 : list Y) : list (X * Y) :=
  match l1, l2 with
  | _, nil => nil
  | nil, _ => nil
  | cons h1 tl1, cons h2 tl2 => cons (h1, h2) (combine tl1 tl2)
  end.


Compute combine [1; 2] [true; false; true].


Fixpoint split { X Y : Type} (l : list (X * Y)) : ((list X) * (list Y)) :=
  match l with
  | nil => (nil, nil)
  | cons (hx, hy) tl => 
    match (split tl) with
    | (lx, ly) => (cons hx lx, cons hy ly)
    end
  end.

Example test_split :
  split [(1, true); (2, false)] = ([1; 2], [true; false]).
Proof.
  simpl.
  reflexivity.
Qed.


Module OptionPlayground.
  Inductive option (X : Type) : Type :=
  | None
  | Some (x : X).

  Arguments Some {X}.
  Arguments None {X}.
End OptionPlayground.


Fixpoint nth_err {X : Type} (l : list X) (n : nat) : option X :=
  match n, l with
  | O, h :: tl => Some h
  | _, nil => None
  | S n', h :: tl => nth_err tl n'
  end.

Example test_nth_err1 :
  nth_err [4;5;6;7] 0 = Some 4.
Proof.
  simpl.
  reflexivity.
Qed.


Example test_nth_err2 :
  nth_err [[1];[2]] 1 = Some [2].
Proof.
  simpl.
  reflexivity.
Qed.

Example test_nth_err3 :
  nth_err [true] 2 = None.
Proof.
  simpl.
  reflexivity.
Qed.


Definition hd_err {X : Type} (l : list X) : option X :=
  match l with
  | nil => None
  | h :: _ => Some h
  end.


Check @hd_err : forall (X : Type), list X -> option X.

Example test_hd_err1 :
  hd_err [1; 2] = Some 1.
Proof.
  simpl.
  reflexivity.
Qed.

Example test_hd_err2 :
  hd_err [[1]; [2]] = Some [1].
Proof.
  simpl.
  reflexivity.
Qed.


(* Higher-Order Functions *)

Definition doit3times {X : Type} (f : X -> X) (n : X) : X :=
  f (f (f n)).


Check @doit3times : forall (X : Type), (X -> X) -> X -> X.


Example test_doit3times :
  doit3times minustwo 9 = 3.
Proof.
  (* compute. *)
  reflexivity.
Qed.

Example test_doit3times' :
  doit3times negb true = false.
Proof.
  (* compute. *)
  reflexivity.
Qed.


Fixpoint filter {X : Type} (test : X -> bool) (l : list X) : (list X) :=
  match l with
  | nil => nil
  | h :: tl =>
    match test h with
    | true => h :: (filter test tl)
    | false => (filter test tl)
    end
  end.


Example test_filter1 :
  filter even [1;2;3;4] = [2;4].
Proof.
  simpl.
  reflexivity.
Qed.


Definition length_is_1 {X : Type} (l : list X) : bool :=
  length l =? 1.


Example test_filter2 :
  filter length_is_1 [[1;2];[3];[4];[5;6;7];[];[8]] = [[3];[4];[8]].
Proof.
  simpl.
  reflexivity.
Qed.


Definition countoddmember' (l : list nat) : nat :=
  length (filter odd l).


Example test_countoddmember'1 :
  countoddmember' [1;0;3;1;4;5] = 4.
Proof.
  compute.
  reflexivity.
Qed.

Example test_countoddmember'2 :
  countoddmember' [0;2;4] = 0.
Proof.
  compute.
  reflexivity.
Qed.

Example test_countoddmember'3 :
  countoddmember' nil = 0.
Proof.
  compute.
  reflexivity.
Qed.


(* Anonymous Functions *)

Example test_anno_fun' :
  doit3times (fun n => n * n) 2 = 256.
Proof.
  reflexivity.
Qed.


Example test_filter2' :
  filter (fun l => length l =? 1)
    [[1;2];[3];[4];[5;6;7];[];[8]] = [[3];[4];[8]].
Proof.
  simpl.
  reflexivity.
Qed.


Definition filter_even_gt7 (l : list nat) : list nat:=
  filter (fun n => (even n) && (n >=? 7)) l.


Example test_filter_even_gt7 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof.
  compute.
  reflexivity.
Qed.


Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof.
  compute.
  reflexivity.
Qed.


Definition partition {X : Type} (f : X -> bool) (l : list X) : ((list X) * (list X)) :=
  (filter f l, filter (fun n => negb (f n)) l).


Example test_patition1 :
  partition odd [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof.
  compute.
  reflexivity.
Qed.


Example test_partition2 :
  partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof.
  compute.
  reflexivity.
Qed.


Fixpoint map {X Y : Type} (f : X -> Y) (l : list X) : (list Y) :=
  match l with
  | nil => nil
  | h :: tl => (f h) :: (map f tl)
  end.


Example test_map1 :
  map (fun x => plus x 3) [2;0;2] = [5;3;5].
Proof.
  compute.
  reflexivity.
Qed.



Example test_map3:
  map (fun n => [even n; odd n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof.
  compute.
  reflexivity.
Qed.


Lemma map_app_distr :
  forall (X Y : Type) (f : X -> Y) (l1 l2 : list X),
  map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof.
  intros.
  induction l1 as [| l1'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite IHl1.
    reflexivity. 
Qed.



Theorem map_rev :
  forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros.
  induction l as [| l'].
  - simpl.
    reflexivity.
  - simpl.
    rewrite <- IHl.
    simpl.
    rewrite map_app_distr.
    reflexivity. 
Qed.


Fixpoint flat_map {X Y : Type} (f : X -> list Y) (l : list X) : list Y :=
  match l with
  | nil => nil
  | h :: tl => (f h) ++ (flat_map f tl)
  end.


Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof.
  compute.
  reflexivity.
Qed.


Definition option_map {X Y : Type} (f : X -> Y) (ox : option X) : option Y :=
  match ox with
  | None => None
  | Some x => Some (f x)
  end.


Fixpoint fold {X Y : Type} (f : X -> Y -> Y) (l : list X) (acc : Y) : Y :=
  match l with
  | nil => acc
  | h :: tl => f h (fold f tl acc)
  end.


Example test_fold1 :
  fold plus [1;2;3;4] 0 = 10.
Proof.
  compute.
  reflexivity.
Qed.


Check (fold andb) : list bool -> bool -> bool.

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof.
  compute.
  reflexivity.
Qed.



Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof.
  compute.
  reflexivity.
Qed.


Example fold_example3 :
  fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof.
  compute.
  reflexivity.
Qed.


Definition constfun {X : Type} (x : X) : nat -> X :=
  fun (k : nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 :
  ftrue 0 = true.
Proof.
  compute.
  reflexivity.
Qed.



Example constfun_example2 : (constfun 5) 99 = 5.
Proof.
  compute.
  reflexivity.
Qed.


Check plus : nat -> nat -> nat.

Definition plus3 := plus 3.

Check plus3 : nat -> nat.


Example test_plus3 : plus3 4 = 7.
Proof.
  compute.
  reflexivity.
Qed.

Example test_plus3' : doit3times plus3 0 = 9.
Proof.
  compute.
  reflexivity.
Qed.

Example test_plus3'' : doit3times (plus 3) 0 = 9.
Proof.
  compute.
  reflexivity.
Qed.


Module Exercises.
  Definition fold_length {X : Type} (l : list X) : nat :=
    fold (fun _ acc => S acc) l 0.
    
  Example test_fold_length1 : fold_length [4;7;0] = 3.
  Proof.
    compute.
    reflexivity.
  Qed.

  (* Lemma fole_length_: .
  Proof.
    
  Qed. *)
  

  Theorem fold_length_correct : forall (X : Type) (l : list X),
    fold_length l = length l.
  Proof.
    induction l as [|l'].
    - simpl.
      reflexivity.
    - simpl.
      rewrite <- IHl. 
      reflexivity.
  Qed.

  Definition fold_map {X Y : Type} (f : X -> Y) (l : list X) : list Y :=
    fold (fun h acc => (f h) :: acc) l [].
  
  Theorem fold_map_correct :
    forall (X Y : Type) (f : X -> Y) (l : list X),
    fold_map f l = map f l.
  Proof.
    intros.
    induction l as [|l'].
    - simpl.
      compute.
      reflexivity.
    - simpl.
      rewrite <- IHl.
      reflexivity.
  Qed.
  
(* 
  It is possible to convert a function between these two types.
  Converting from X × Y → Z to X → Y → Z is called currying, in
  honor of the logician Haskell Curry. Converting from X → Y → Z
  to X × Y → Z is called uncurrying.
*)

  Definition prod_curry {X Y Z : Type} (f : X * Y -> Z) (x : X)
                                       (y : Y) : Z :=
    f (x, y).

  Definition prod_uncurry {X Y Z : Type} (f : X -> Y -> Z)
                                         (p: X * Y) : Z :=
    match p with
    | (x, y) => f x y
    end.
  
  Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
  Proof.
    compute.
    reflexivity.
  Qed.

  Check @prod_curry.
  Check @prod_uncurry.

  Theorem uncurry_curry :
    forall (X Y Z : Type) (f : X -> Y -> Z) (x : X) (y : Y),
    prod_curry (prod_uncurry f) x y = f x y.
  Proof.
    intros.
    compute.
    reflexivity.
  Qed.

  Theorem curry_uncurry :
    forall (X Y Z : Type) (f : (X * Y) -> Z) (p : X * Y),
    prod_uncurry (prod_curry f) p = f p.
  Proof.
    intros.
    destruct p.
    simpl.
    compute.
    reflexivity.
  Qed.

  Theorem nth_err_formal:
    forall (X : Type) (l : list X) (n : nat),
    length l = n -> @nth_err X l n = None.
  Proof.
    intros.
    induction l as [|l'].
    - rewrite <- H.
      simpl.
      reflexivity.
    - rewrite <- H.
      simpl.
      rewrite <- IHl.
  Admitted.

Module Church. 
  Definition cnat :=
    forall (X : Type), (X -> X) -> X -> X.

  Definition zero : cnat :=
    fun (X : Type) (succ : X -> X) (zero : X) => zero.

  Definition one : cnat :=
    fun (X : Type) (succ : X -> X) (zero : X) => succ zero.
  
  Definition two : cnat :=
    fun (X : Type) (succ : X -> X) (zero : X) => succ (succ zero).

  Definition three : cnat := @doit3times.
  

  Example zero_church_peano : zero nat S O = 0.
  Proof.
    compute.
    reflexivity.
  Qed.

  Example one_church_peano : one nat S O = 1.
  Proof.
    reflexivity.
  Qed.

  Example two_church_peano : two nat S O = 2.
  Proof.
    reflexivity.
  Qed.

  Definition scc (n : cnat) : cnat :=
    fun (X : Type) (succ : X -> X) (x : X) => succ (n X succ x).

  Example scc_1 : scc zero = one.
  Proof.
    reflexivity.
  Qed.

  Example scc_2 : scc one = two.
  Proof.
    reflexivity.
  Qed.

  Example scc_3 : scc two = three.
  Proof.
    reflexivity.
  Qed.
    
  Definition plus (n m : cnat) : cnat :=
    fun (X : Type) (succ : X -> X) (x : X) =>
      n X succ (m X succ x).

  Example plus_1 : plus zero one = one.
  Proof.
    reflexivity.
  Qed.

  Example plus_2 : plus two three = plus three two.
  Proof.
    reflexivity.
  Qed.

  Example plus_3 :
    plus (plus two two) three = plus one (plus three three).
  Proof.
    reflexivity.
  Qed.

  Definition mult (n m : cnat) : cnat :=
    fun (X : Type) (succ : X -> X) (x : X) =>
      (n X (fun x' => m X succ x')) x.
  
  Example mult_1 : mult one one = one.
  Proof.
    reflexivity.
  Qed.

  Example mult_2 : mult zero (plus three three) = zero.
  Proof.
    reflexivity.
  Qed.

  Example mult_3 : mult two three = plus three three.
  Proof.
    reflexivity.
  Qed.


  Definition exp (n m : cnat) : cnat :=
    fun (X : Type) (succ : X -> X) (x : X) =>
      (m (X -> X) (n X) succ) x.


  Example exp_1 : exp two two = plus two two.
  Proof.
    reflexivity.
  Qed.

  Example exp_2 : exp three zero = one.
  Proof.
    reflexivity.
  Qed.

  Example exp_3 : exp three two = plus (mult two (mult two two)) one.
  Proof.
    reflexivity.
  Qed.

End Church.
End Exercises.
