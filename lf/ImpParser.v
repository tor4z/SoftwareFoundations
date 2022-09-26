From Coq Require Import Strings.String.
From Coq Require Import Strings.Ascii.
From Coq Require Import Arith.Arith.
From Coq Require Import Init.Nat.
From Coq Require Import Arith.EqNat.
From Coq Require Import Lists.List. Import ListNotations.
From LF Require Import Imp.


Definition isWhite (c : ascii) : bool :=
  let n := nat_of_ascii c in 
  match n with
  | 32 => true  (* space *)
  | 9 => true   (* tab *)
  | 10 => true  (* linefeed *)
  | 13 => true  (* Carriage return *)
  | _ => false
  end.

Notation "x '<=?' y" := (x <=? y).

Definition isLowerAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (97 <=? n) (n <=? 122).

Definition isAlpha (c : ascii) : bool :=
  let n := nat_of_ascii c in
    orb (andb (65 <=? n) (n <=? 90))
        (andb (97 <=? n) (n <=? 122)).

Definition isDigit (c : ascii) : bool :=
  let n := nat_of_ascii c in
    andb (48 <=? n) (n <=? 57).

Inductive charType : Type :=
| white
| alpha
| digit
| other.

Definition classifyChar (c : ascii) : charType :=
  if isWhite c then white
  else if isAlpha c then alpha
  else if isDigit c then digit
  else other.

Fixpoint listOfString (s : string) : list ascii :=
  match s with
  | EmptyString => []
  | String c s => c :: (listOfString s)
  end.

Definition stringOfList (xs : list ascii) : string :=
  fold_right String EmptyString xs.

Definition token := string.

Fixpoint tokenize_helper (cls : charType) (acc xs : list ascii)
                         : list (list ascii) :=
  let tk := match acc with
  | [] => []
  | _ :: _ => [rev acc]
  end in
  match xs with
  | [] => tk
  | (x :: xs') =>
    match cls, classifyChar x, x with
    | _, _, "(" => tk ++ ["("] :: (tokenize_helper other [] xs')
    | _, _, ")" => tk ++ [")"] :: (tokenize_helper other [] xs')
    | _, white, _ => tk ++ (tokenize_helper white [] xs')
    | alpha, alpha, x => tokenize_helper alpha (x::acc) xs'
    | digit, digit, x => tokenize_helper digit (x::acc) xs'
    | other, other, x => tokenize_helper other (x::acc) xs'
    | _, tp, x => tk ++ (tokenize_helper tp [x] xs')
    end
  end % char.

Definition tokenize (s : string) : list string :=
  map stringOfList (tokenize_helper white [] (listOfString s)).

Example tokenize_ex1 :
  tokenize "abc12=3 223*(3+(a+c))" % string
  = ["abc"; "12"; "="; "3"; "223";
     "*"; "("; "3"; "+"; "(";
     "a"; "+"; "c"; ")"; ")"] % string.
Proof.
  compute.
  reflexivity.
Qed.



Inductive optionE (X : Type) : Type :=
| SomeE (x : X)
| NoneE (s : string).


Arguments SomeE {X}.
Arguments NoneE {X}.


Notation "' p <- e1 ;; e2" :=
  (
    match e1 with
    | SomeE p => e2
    | NoneE err => NoneE err
    end
  )
  (right associativity, p pattern, at level 60,
    e1 at next level).

Notation "'TRY' ' p <- e1 ;; e2 'OR' e3" :=
  (
    match e1 with
    | SomeE p => e2
    | NoneE _ => e3
    end
  )
  (right associativity, p pattern, at level 60,
    e1 at next level, e2 at next level).


Open Scope string_scope.

Definition parser (T : Type) :=
  list token -> optionE (T * list token).

Fixpoint many_helper {T} (p : parser T) acc steps xs :=
  match steps, p xs with
  | 0, _ => NoneE "Too many recursive calls"
  | _, NoneE _ => SomeE ((rev acc), xs)
  | S steps', SomeE (t, xs') => many_helper p (t::acc) steps' xs'
  end.

Definition many {T} (p : parser T) (steps : nat) : parser (list T) :=
  many_helper p [] steps.

Definition firstExpect {T} (t : token) (p : parser T) : parser T :=
  fun xs =>
    match xs with
    | x :: xs' =>
      if string_dec x t then p xs'
      else NoneE ("expected '" ++ t  ++ "'.")
    | [] => NoneE ("expected '" ++ t  ++ "'.")
    end.

Definition expect (t : token) : parser unit :=
  firstExpect t (fun xs => SomeE (tt, xs)).

Definition parseIdentifier (xs : list token)
                          : optionE (string * list token) :=
  match xs with
  | [] => NoneE "Expected identifier"
  | x :: xs' =>
    if forallb isLowerAlpha (listOfString x) then SomeE (x, xs')
    else NoneE ("Illegal identifier: '" ++ x ++ "'")
  end.

Definition parseNumber (xs : list token)
                      : optionE (nat * list token) :=
  match xs with
  | [] => NoneE "Expected number"
  | x :: xs' =>
    if forallb isDigit (listOfString x) then
      SomeE (fold_left
        (fun n d =>
          10 * n + (nat_of_ascii d - nat_of_ascii "0"%char)
        )
        (listOfString x)
        0,
      xs')
    else
      NoneE "Expected number"
  end.


