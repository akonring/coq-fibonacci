(* Fibonacci Sequence 

   File: 'fibonacci.v'

   Description: This file is about
   fibonacci functions and specifications
   several identities will be proved
   about the famous Fibonacci sequence *)

Require Import Arith.

(* Default specification of fibonacci

   Specification of Fibonacci from
   'fibonacci-with-some-solutions.v' *)
   
Definition specification_of_fibonacci (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  forall n'' : nat,
    fib (S (S n'')) = fib (S n'') + fib n''.


(* Alternative specification of Fibonacci

   Specification of Fibonacci from
   'fibonacci-with-some-solutions.v' *)

Definition specification_of_fibonacci_alt (fib : nat -> nat) :=
  fib 0 = 0
  /\
  fib 1 = 1
  /\
  fib 2 = 1
  /\
  forall p q : nat,
    fib (S (p + q)) =
    fib (S p) * fib (S q) + fib p * fib q.


(* Alternative version of nat_ind

   From 'fibonacci-with-some-solutions.v'.
   This implementation uses two
   induction base-cases and hypotheses to 
   better fit the Fibonacci definition *)

Lemma nat_ind2 :
  forall P : nat -> Prop,
    P 0 ->
    P 1 ->
    (forall i : nat,
      P i -> P (S i) -> P (S (S i))) ->
    forall n : nat,
      P n.
Proof.
  intros P H_bc0 H_bc1 H_ic n.
  assert (both : P n /\ P (S n)).
    induction n as [ | n' [IH_n' IH_Sn']].
    split.
    apply H_bc0.
    apply H_bc1.
    split.
    apply IH_Sn'.
    apply (H_ic n' IH_n' IH_Sn').
  destruct both as [H_n _].
  apply H_n.
Qed.

(* Uniqueness of Fibonacci function

   Two functions which satisfies the specification
   does indeed yield the same result for all natural number *)

Theorem there_is_only_one_fibonacci :
  forall fib1 fib2 : nat -> nat,
    specification_of_fibonacci fib1 ->
    specification_of_fibonacci fib2 ->
    forall n : nat,
      fib1 n = fib2 n.
Proof.
  intros fib1 fib2.
  unfold specification_of_fibonacci.
  intros [H_fib1_bc0 [H_fib1_bc1 H_fib1_ic]]
         [H_fib2_bc0 [H_fib2_bc1 H_fib2_ic]].
  intro n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  rewrite H_fib2_bc0.
  apply H_fib1_bc0.

  rewrite H_fib2_bc1.
  apply H_fib1_bc1.

  rewrite H_fib1_ic.
  rewrite H_fib2_ic.
  rewrite IHn'.
  rewrite IHSn'.
  reflexivity.
Qed.

Theorem there_is_only_one_fibonacci_with_alt :
  forall fib1 fib2 : nat -> nat,
    specification_of_fibonacci_alt fib1 ->
    specification_of_fibonacci_alt fib2 ->
    forall n : nat,
      fib1 n = fib2 n.
Proof.
  intros fib1 fib2.
  unfold specification_of_fibonacci_alt.
  intros [H_fib1_bc0 [H_fib1_bc1 [H_fib1_bc2 H_fib1_ic]]]
         [H_fib2_bc0 [H_fib2_bc1 [H_fib2_bc2 H_fib2_ic]]].
  intro n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  rewrite H_fib2_bc0.
  apply H_fib1_bc0.

  rewrite H_fib2_bc1.
  apply H_fib1_bc1.

  rewrite <- (plus_0_r (S n')).
  rewrite plus_Sn_m.
  rewrite plus_n_Sm.
  rewrite H_fib1_ic.
  rewrite H_fib2_ic.
  rewrite IHSn'.
  rewrite IHn'.
  rewrite H_fib1_bc1.
  rewrite H_fib1_bc2.
  rewrite H_fib2_bc1.
  rewrite H_fib2_bc2.
  reflexivity.
Qed.


(* Useful helper functions *)

Lemma unfold_plus_induction_case :
  forall i j : nat,
    (S i) + j = S (i + j).
Proof.
  intros i j; unfold plus; reflexivity.
Qed.

Lemma increment :
  forall n : nat,
    S n = 1 + n.
Proof.
  intro n.
  rewrite -> unfold_plus_induction_case.
  rewrite -> plus_0_l.
  reflexivity.
Qed.

Lemma unfold_mult_induction_case :
  forall i j : nat,
    (S i) * j = j + (i * j).
Proof.
  intros i j; unfold mult; reflexivity.
Qed.

Lemma plus_2_mult :
  forall i : nat,
    i + i = 2*i.
Proof.
  intro i. 
  rewrite unfold_mult_induction_case.
  rewrite mult_1_l.
  reflexivity.
Qed.

Definition square (x : nat) : nat :=
  x * x.

Lemma unfold_square :
  forall x : nat, square x = x * x.
Proof.
  intro x; unfold square; reflexivity.
Qed.

Lemma binomial_2 :
  forall x y : nat,
    square (x + y) = square x + 2 * x * y + square y.
Proof.
  intros x y.
  rewrite -> unfold_square.
  rewrite -> mult_plus_distr_l.
  rewrite ->2 mult_plus_distr_r.
  rewrite -> (mult_comm y x).
  rewrite -> plus_assoc.
  assert (L : forall a b c : nat,
                a + b + b + c = a + 2 * b + c).
    intros a b c.
    unfold mult.
    rewrite -> plus_0_r.
    rewrite -> plus_assoc.
    reflexivity.
  rewrite -> L.
  rewrite -> mult_assoc.
  reflexivity.
Qed.

Lemma plus_comm_over_paren_r : 
  forall a b c,
    (a + b) + c = (a + c) + b.
Proof.
  intros a b c.
  rewrite <- plus_assoc.
  rewrite (plus_comm b c).
  rewrite plus_assoc.
  reflexivity.
Qed.


(* Equivalence of default and alternative 
   specification of Fibonacci

   This proposition shows that if one
   function satisfies one version of
   the fibonacci specifications then the same function
   also fits the other specification *)

Proposition equivalence_of_the_specifications_of_fibonacci :
  forall fib: nat -> nat,
    specification_of_fibonacci fib
    <->
    specification_of_fibonacci_alt fib.
Proof.
  intro fib.
  unfold specification_of_fibonacci.
  unfold specification_of_fibonacci_alt.
  split.
  intro H_fib.
  destruct H_fib as [H_fib_bc0 [H_fib_bc1 H_fib_ic]].
  split.
  rewrite H_fib_bc0.
  reflexivity.
  split.
  rewrite H_fib_bc1.
  reflexivity.
  split.
  rewrite H_fib_ic.
  rewrite H_fib_bc0.
  rewrite H_fib_bc1.
  rewrite plus_0_r.
  reflexivity.
  intro p.
  induction p as [ | | p' IH_p' IH_Sp'] using nat_ind2.
  intro q.
  rewrite plus_0_l.
  rewrite H_fib_bc0.
  rewrite mult_0_l.
  rewrite plus_0_r.
  rewrite H_fib_bc1.
  rewrite mult_1_l.
  reflexivity.

  intro q.
  rewrite (H_fib_ic 0).
  rewrite H_fib_bc0.
  rewrite plus_0_r.
  rewrite H_fib_bc1.
  rewrite 2 mult_1_l.
  rewrite H_fib_ic.
  reflexivity.

  intro q.
  rewrite 2 H_fib_ic.
  rewrite 3 mult_plus_distr_r.
  rewrite (plus_comm (fib (S p') * fib q)). 
  rewrite plus_assoc.
  rewrite <- (plus_assoc (fib (S p') * fib (S q) + fib p' * fib (S q))).
  rewrite <- IH_p'.
  rewrite <- mult_plus_distr_r.
  rewrite <- H_fib_ic.
  rewrite <- plus_assoc.
  rewrite <- (plus_comm (fib (S p') * fib q)).
  rewrite plus_assoc.
  rewrite <- IH_Sp'.
  rewrite <- H_fib_ic.
  reflexivity.

(* specification_of_fibonacci fib
   <-
   specification_of_fibonacci_alt fib. *)

  intro H_fib.
  destruct H_fib as [H_fib_bc0 [H_fib_bc1 [H_fib_bc2 H_fib_ic]]].
  split.
  rewrite H_fib_bc0.
  reflexivity.
  split.
  rewrite H_fib_bc1.
  reflexivity.
  intro n.
  rewrite increment.
  rewrite <- plus_n_Sm.
  rewrite H_fib_ic.
  rewrite H_fib_bc2.
  rewrite H_fib_bc1.
  rewrite 2 mult_1_l.
  reflexivity.
Qed.

(* Uniqueness of fibonacci could be shown in two ways.
   Here by assuming there is only one fibonacci. *)

Proposition uniqueness_of_fibonacci :
  (forall fib1 fib2 : nat -> nat,
    specification_of_fibonacci fib1 ->
    specification_of_fibonacci fib2 ->
    forall n : nat,
      fib1 n = fib2 n)
  <->
  (forall fib1 fib2 : nat -> nat,
     specification_of_fibonacci_alt fib1 ->
     specification_of_fibonacci_alt fib2 ->
     forall n : nat,
       fib1 n = fib2 n).
Proof.
  split.
  intro H_spec1.
  apply there_is_only_one_fibonacci_with_alt.

  (* intro H_spec2.
     apply there_is_only_one_fibonacci. *)
  intro H_spec2.
  intros fib1 fib2.
  intro H_spec_fib1.
  intro H_spec_fib2.
  intro n.

  unfold specification_of_fibonacci in H_spec_fib1.
  unfold specification_of_fibonacci in H_spec_fib2.

  destruct H_spec_fib1 as [H_fib1_bc0 [H_fib1_bc1  H_fib1_ic]].
  destruct H_spec_fib2 as [H_fib2_bc0 [H_fib2_bc1  H_fib2_ic]].
  
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  rewrite H_fib2_bc0.
  apply H_fib1_bc0.

  rewrite H_fib2_bc1.
  apply H_fib1_bc1.

  rewrite H_fib1_ic.
  rewrite H_fib2_ic.
  rewrite IHSn'.
  rewrite IHn'.
  reflexivity.
Qed.

  
(* Finnr the Finder's proposition

   From 'fibonacci-with-some-solutions.v'
   The function from dProgSprog Exam 2013
   is a clever identity proved using
   the 'nat_ind2' combinator which makes sure that the proof
   has two induction hypotheses. *)

Proposition about_fib_of_a_sum :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall p q : nat,
      fib (S (p + q)) = fib (S p) * fib (S q) + fib p * fib q.
Proof.
  intro fib.
  unfold specification_of_fibonacci.
  intros [fib_bc0 [fib_bc1 fib_ic]].
  intro n.
  induction n as [ | | n' IHn' IH_Sn'] using nat_ind2.
  intro q.
  rewrite plus_0_l.
  rewrite fib_bc1.
  rewrite fib_bc0.
  rewrite mult_0_l.
  rewrite mult_1_l.
  rewrite plus_0_r.
  reflexivity.

  intro q.
  rewrite fib_ic.
  rewrite fib_bc1.
  rewrite fib_ic.
  rewrite fib_bc1.
  rewrite fib_bc0.
  rewrite 2 mult_1_l.
  reflexivity.

  intro q.
  rewrite fib_ic.
  rewrite mult_plus_distr_r.
  rewrite fib_ic.
  rewrite mult_plus_distr_r.
  rewrite mult_plus_distr_r.
  rewrite plus_comm_over_paren_r.
  rewrite plus_assoc.
  rewrite <- plus_assoc.
  rewrite <- (plus_comm (fib (S n') * fib (S q))).
  rewrite <- IHn'.
  rewrite <- mult_plus_distr_r.
  rewrite <- fib_ic.
  rewrite <- IH_Sn'.
  rewrite <- fib_ic.
  reflexivity.
Qed.  


(* d'Ocagne's identity 

   This identity is really just a
   special case of Finnr the Finder's proposition
   where p := n and q := S n *)

Proposition d_Ocagne_s_identity :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall n : nat,
      fib (2 * (S n)) = fib (S n) * (fib (S (S n)) + fib n).
Proof.
  intro fib.
  intro H_specification_of_fibonacci.
  assert (H_tmp := H_specification_of_fibonacci).
  unfold specification_of_fibonacci in H_specification_of_fibonacci.
  destruct H_specification_of_fibonacci as [fib_bc0 [fib_bc1 fib_ic]].
  intro n.
  rewrite mult_plus_distr_l.
  rewrite <- (mult_comm (fib (S (S n))) (fib (S n))). 
  rewrite <- (about_fib_of_a_sum fib H_tmp (S n) n).
  rewrite mult_succ_l.
  rewrite mult_1_l.
  rewrite plus_Sn_m.
  rewrite <- plus_n_Sm.
  reflexivity.
Qed.


(* Cassini's identity for odd numbers
   
   The proof strategy is to use induction
   and apply the induction hypotheses.
   And then reduce to apply the binomial2 *)

Proposition Cassini_s_identity_for_odd_numbers :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall n : nat,
      square (fib (S (2 * n))) =
      S ((fib (2 * (S n))) * (fib (2 * n))).
Proof.
  intro fib.
  unfold specification_of_fibonacci.
  intros [fib_bc0 [fib_bc1 fib_ic]].
  intro n.
  induction n as [ | n' IHn'] using nat_ind.
  rewrite mult_0_r.
  rewrite fib_bc1.
  rewrite unfold_square.
  rewrite 2 mult_1_r.
  rewrite fib_ic.
  rewrite fib_bc0.
  rewrite fib_bc1.
  rewrite mult_0_r.
  reflexivity.

  rewrite <- 2 plus_2_mult.
  rewrite <- plus_n_Sm at 1.
  rewrite plus_Sn_m.
  rewrite fib_ic.

  rewrite (plus_Sn_m n' (S n')).
  rewrite <- (plus_n_Sm n' n').
  rewrite (fib_ic (n' + n')) at 2.
  rewrite <- (plus_n_Sm (S (S n'))).
  rewrite (plus_Sn_m (S n')).
  rewrite (fib_ic ((S n') + (S n'))).
  rewrite plus_Sn_m at 1.
  rewrite <- (plus_n_Sm n').
  rewrite (fib_ic (S (n' + n'))).
  rewrite mult_plus_distr_r.  
  rewrite (mult_plus_distr_l (fib (S n' + S n'))).
  rewrite (plus_2_mult (S n')).
  rewrite (plus_2_mult n').
  rewrite (plus_n_Sm ((fib (S (S (2 * n'))) + fib (S (2 * n'))) *
      (fib (S (2 * n')) + fib (2 * n')))).
  rewrite (plus_n_Sm (fib (2 * S n') * fib (S (2 * n')))).
  rewrite <- IHn'.
  rewrite plus_assoc.

(* Since (F(2n+2) + F(2n+1))^2 = 
         (F(2n+1)^2 + Rest)
         =>
         Rest = F(2n+2)^2 + 2 * F(2n+2) * F(2n+1) *)

  assert (H_bin : forall n' : nat,
                 square (fib (S (S (2 * n')))) + 2 * fib (S (S (2 * n'))) * fib (S (2 * n')) =
                 (fib (S (S (2 * n'))) + fib (S (2 * n'))) *
                 (fib (S (2 * n')) + fib (2 * n')) +
                 (fib (2 * S n') * fib (S (2 * n')))).
    intro n''.
    rewrite <- (plus_2_mult n'').
    rewrite <- (plus_2_mult (S n'')).
    rewrite mult_plus_distr_r.
    rewrite <- fib_ic.
    rewrite <- unfold_square.
    rewrite (mult_comm (fib (S (n'' + n'')))).
    rewrite <- plus_assoc.
    rewrite <- mult_plus_distr_r.
    rewrite plus_Sn_m.
    rewrite <- plus_n_Sm.
    rewrite 2 plus_2_mult.
    reflexivity.

  rewrite <- (H_bin n').
  rewrite <- binomial_2.
  reflexivity.
Qed.

  
(* Cassini's identity for even numbers *)

Proposition Cassini_s_identity_for_even_numbers :
  forall fib : nat -> nat,
    specification_of_fibonacci fib ->
    forall n : nat,
      S (square (fib (2 * (S n)))) =
      (fib (S (2 * (S n)))) * (fib (S (2 * n))).
Proof.
  intro fib.
  intro H_specification_of_fibonacci.
  unfold specification_of_fibonacci in H_specification_of_fibonacci.
  destruct H_specification_of_fibonacci as [fib_bc0 [fib_bc1 fib_ic]].
  intro n.
  induction n as [ | n' IHn'] using nat_ind.
  rewrite mult_0_r.
  rewrite fib_bc1.
  rewrite 2 mult_1_r.
  rewrite unfold_square.
  rewrite 3 fib_ic.
  rewrite fib_bc0.
  rewrite fib_bc1.
  rewrite plus_0_r.
  rewrite mult_1_r.
  rewrite plus_Sn_m.
  rewrite plus_0_l.
  reflexivity.

  rewrite <- 2 plus_2_mult.
  rewrite <- (plus_n_Sm (S n')).
  rewrite fib_ic.
  rewrite <- plus_n_Sm.
  rewrite plus_Sn_m.
  rewrite (fib_ic (S (S n' + S n'))).
  rewrite (fib_ic (S n' + S n')).
  rewrite 2 mult_plus_distr_r.
  rewrite 2 mult_plus_distr_l.
  rewrite (plus_Sn_m n' n') at 6.
  rewrite (plus_2_mult n').
  rewrite (plus_2_mult (S n')) at 8.
  rewrite <- IHn'.
  rewrite <- plus_2_mult.
  rewrite <- 2 mult_plus_distr_l.
  rewrite (plus_Sn_m n' n').
  rewrite <- (fib_ic (S (n' + n'))).
  rewrite <- mult_plus_distr_r.
  rewrite plus_assoc.
  rewrite <- (plus_n_Sm ((fib (S (S n' + S n')) + fib (S n' + S n')) * fib (S (S (S (n' + n')))) +
   (fib (S (S n' + S n')) * fib (S (S (n' + n')))))).
  
(* Since (F(2n+3) + F(2n+2))^2 + 1 = 
         (F(2n+2)^2 + Rest) + 1
         =>
         Rest = F(n+3)^2 + 2 * F(n+3) * F(n+2) *)

  assert (H_bin' : forall n' : nat,
                 square (fib (S (S n' + S n'))) + 2 * fib (S (S n' + S n')) * fib (S n' + S n') =
                 (fib (S (S n' + S n')) + fib (S n' + S n')) * fib (S (S (S (n' + n')))) +
                 fib (S (S n' + S n')) * fib (S (S (n' + n')))).
    intro n''.
    rewrite (plus_Sn_m n'').
    rewrite <- (plus_n_Sm n'').
    rewrite mult_plus_distr_r.
    rewrite <- unfold_square.
    rewrite <- plus_assoc.
    rewrite (mult_comm (fib (S (S (n'' + n''))))).
    rewrite (plus_2_mult (fib (S (S (S (n'' + n'')))) * fib (S (S (n'' + n''))))).
    rewrite mult_assoc.
    reflexivity.

  rewrite <- (H_bin' n').
  rewrite <- binomial_2.
  reflexivity.
Qed.

(* end of 'fibonacci.v' *)
