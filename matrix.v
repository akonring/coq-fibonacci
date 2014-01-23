(* Matrix manipulation 

   File: 'matrix.v'

   Description: The main purpose of this file
   is to make available the necessary operations
   on matrices to test identities of the fibonacci
   sequence *)
   
Require Import Arith.

Require Import Lists.List.

(* Coq library from the fibonacci.v file

   Compile by entering the following in command line
   > coqc fibonacci.v *)

Require Import fibonacci.


(* A 2x2 matrix is a simple constructor
   with 4 nats.

   |a00 a01|
   |a10 a11|

*)

Inductive matrix22 :=
| Matrix22 : nat -> nat -> nat -> nat -> matrix22.


Definition matrix_1 := Matrix22 1 2 3 4.
Definition matrix_2 := Matrix22 5 6 7 8.
Definition matrix_3 := Matrix22 9 8 7 6.


(* The identity matrix

   |1 0|
   |0 1|

*)

Definition matrix_identity := Matrix22 1 0 0 1.

Lemma unfold_matrix_identity :
  matrix_identity = Matrix22 1 0 0 1.
Proof.
  unfold matrix_identity.
  reflexivity.
Qed.


(* Addition of two matrices *)

Definition matrix_plus (m m' : matrix22) : matrix22 :=
  match (m, m') with
    | (Matrix22 a00 a01 a10 a11, Matrix22 b00 b01 b10 b11)
      => Matrix22 (a00 + b00) (a01 + b01) (a10 + b10) (a11 + b11)
  end. 
  

Lemma unfold_matrix_plus :  
  forall m m' : matrix22,
    matrix_plus m m' = 
    match (m, m') with
      | (Matrix22 a00 a01 a10 a11, Matrix22 b00 b01 b10 b11)
        => Matrix22 (a00 + b00) (a01 + b01) (a10 + b10) (a11 + b11)
    end. 
Proof.
  unfold matrix_plus.
  reflexivity.
Qed.


(* Addition test

   |1 2|  +  |5 6|  =  | 6  8|
   |3 4|  +  |7 8|  =  |10 12|

*)

Compute matrix_plus matrix_1 matrix_2.

(* Matrix22 6 8 10 12
    : matrix22      *)


(* Scalar product of natural number and matrix *)

Definition matrix_scalar (c : nat) (m : matrix22) :=
  match m with
    | Matrix22 a00 a01 a10 a11
      => Matrix22 (a00 * c) (a01 * c) (a10 * c) (a11 * c)
  end. 

Lemma unfold_matrix_scalar :  
  forall (m : matrix22) (c : nat),
    matrix_scalar c m = 
    match m with
      | Matrix22 a00 a01 a10 a11
        => Matrix22 (a00 * c) (a01 * c) (a10 * c) (a11 * c)
    end. 
Proof.
  unfold matrix_scalar.
  reflexivity.
Qed.

Compute matrix_scalar 10 matrix_1.

(* Matrix22 10 20 30 40
    : matrix22        *)


(* Ordinary matrix multiplication *)

Definition matrix_multiplication (m m' : matrix22) :=
  match (m, m') with
    | (Matrix22 a00 a01 a10 a11, Matrix22 b00 b01 b10 b11)
      => Matrix22 (a00 * b00 + a01 * b10) (a00 * b01 + a01 * b11) (a10 * b00 + a11 * b10) (a10 * b01 + a11 * b11)
  end. 

Lemma unfold_matrix_multiplication :
  forall m m' : matrix22,
    matrix_multiplication m m' = match (m, m') with
    | (Matrix22 a00 a01 a10 a11, Matrix22 b00 b01 b10 b11)
      => Matrix22 (a00 * b00 + a01 * b10) (a00 * b01 + a01 * b11) (a10 * b00 + a11 * b10) (a10 * b01 + a11 * b11)
  end. 
Proof.
  unfold matrix_multiplication.
  reflexivity.
Qed.


(* Multiplication test

   |1 2|  *  |5 6|  =  | 19  22|
   |3 4|  *  |7 8|  =  | 43  50|

*)

Compute matrix_multiplication matrix_1 matrix_2.

(* Matrix22 19 22 43 50
    : matrix22    *)


(* Identity matrix is neutral *)

Lemma matrix_identity_is_neutral_on_the_left :
  forall m : matrix22,
    matrix_multiplication matrix_identity m = m.
Proof.
  intro m.
  rewrite unfold_matrix_identity.
  rewrite unfold_matrix_multiplication.
  case m as [ a00 a01 a10 a11 ].
  rewrite 4 mult_1_l.
  rewrite 4 mult_0_l.
  rewrite 2 plus_0_r.
  rewrite 2 plus_0_l.
  reflexivity.
Qed.


Lemma matrix_identity_is_neutral_on_the_right :
  forall m : matrix22,
    matrix_multiplication m matrix_identity = m.
Proof.
  intro m.
  rewrite unfold_matrix_identity.
  rewrite unfold_matrix_multiplication.
  case m as [ m00 m01 m10 m11 ].
  rewrite 4 mult_1_r.
  rewrite 4 mult_0_r.
  rewrite 2 plus_0_r.
  rewrite 2 plus_0_l.
  reflexivity.
Qed.


(* Matrix multiplication is associative *)

Lemma matrix_multiplication_is_associative :
  forall a b c : matrix22,
    matrix_multiplication (matrix_multiplication a b) c = matrix_multiplication a (matrix_multiplication b c).
Proof.
  intros a b c.
  rewrite 4 unfold_matrix_multiplication.
  destruct a as [a00 a01 a10 a11].
  destruct b as [b00 b01 b10 b11].
  destruct c as [c00 c01 c10 c11].
  rewrite 8 mult_plus_distr_r.
  rewrite 8 mult_plus_distr_l.
  rewrite 16 mult_assoc.
  rewrite 8 plus_assoc.
  rewrite <- (plus_assoc (a00 * b00 * c00)).
  rewrite (plus_comm (a01 * b10 * c00)).
  rewrite <- (plus_assoc (a00 * b00 * c01)).
  rewrite (plus_comm (a01 * b10 * c01)).
  rewrite <- (plus_assoc (a10 * b00 * c00)).
  rewrite (plus_comm (a11 * b10 * c00)).
  rewrite <- (plus_assoc (a10 * b00 * c01)).
  rewrite (plus_comm (a11 * b10 * c01)).
  rewrite 4 plus_assoc.
  reflexivity.
Qed.


(* Multiplication is associative test
  
   (A * B) * C = A * (B * C)
*)

Compute (matrix_multiplication 
        (matrix_multiplication matrix_1 matrix_2) 
         matrix_3) 
        = 
        (matrix_multiplication 
         matrix_1
        (matrix_multiplication  matrix_2 matrix_3)).

(* Matrix22 325 284 737 644 = Matrix22 325 284 737 644
     : Prop  *)


(* Matrix exponentiation function
   
   Base case is defined by the identity
   matrix thus A^0=I *)

Fixpoint matrix_exponentiation (m : matrix22) (n : nat) : matrix22 :=
  match n with
    | 0 => matrix_identity
    | S n' => matrix_multiplication (matrix_exponentiation m n') m
  end.


Lemma unfold_matrix_exponentiation_bc :
  forall (m : matrix22),
    matrix_exponentiation m 0 = matrix_identity.
Proof.
  unfold matrix_exponentiation.
  reflexivity.
Qed.

Lemma unfold_matrix_exponentiation_ic :
  forall (m : matrix22) (n : nat),
    matrix_exponentiation m (S n) = matrix_multiplication (matrix_exponentiation m n) m.
Proof.
  unfold matrix_exponentiation.
  reflexivity.
Qed.


(* Properties of matrix exponentiation 

   This identity is proposition 14
   in dProgSprog notes. *)

Theorem exponentiation_of_a_matrix :
  forall (n : nat),
    matrix_exponentiation (Matrix22 1 1 0 1) n =
    Matrix22 1 n 0 1.
Proof.
  intro n.
  induction n as [ | n' IHn'].
  rewrite unfold_matrix_exponentiation_bc.
  rewrite unfold_matrix_identity.
  reflexivity.
  
  rewrite unfold_matrix_exponentiation_ic.
  rewrite unfold_matrix_multiplication.
  rewrite IHn'.
  rewrite 3 mult_1_r.
  rewrite 2 mult_0_r.
  rewrite 2 plus_0_r.
  rewrite plus_Sn_m.
  rewrite 2 plus_0_l.
  reflexivity.
Qed.


Lemma about_matrix_exponentiation_left :
  forall (a : matrix22) (n : nat),
    matrix_multiplication a (matrix_exponentiation a n) =
    matrix_exponentiation a (S n).
Proof.
  intros a n.
  induction n as [ | n'].
  rewrite unfold_matrix_exponentiation_bc.
  rewrite unfold_matrix_exponentiation_ic.
  rewrite unfold_matrix_exponentiation_bc.
  rewrite matrix_identity_is_neutral_on_the_left.
  rewrite matrix_identity_is_neutral_on_the_right.
  reflexivity.

  rewrite unfold_matrix_exponentiation_ic.
  rewrite unfold_matrix_exponentiation_ic.
  rewrite <- IHn'.
  rewrite matrix_multiplication_is_associative.
  reflexivity.
Qed.

Lemma about_matrix_exponentiation_right :
  forall (a : matrix22) (n : nat),
    matrix_multiplication (matrix_exponentiation a n) a =
    matrix_exponentiation a (S n).
Proof.
  intros a n.
  induction n as [ | n'].
  rewrite unfold_matrix_exponentiation_bc.
  rewrite unfold_matrix_exponentiation_ic.
  rewrite unfold_matrix_exponentiation_bc.
  rewrite matrix_identity_is_neutral_on_the_left.
  reflexivity.

  rewrite unfold_matrix_exponentiation_ic.
  rewrite unfold_matrix_exponentiation_ic.
  rewrite <- IHn'.
  reflexivity.
Qed.


(* Proposition 29 in dProgSprog notes *)

Proposition about_matrix_exponentiation :
  forall (m : matrix22) (n : nat),
    matrix_multiplication (matrix_exponentiation m n) m =
    matrix_multiplication m (matrix_exponentiation m n).
Proof.
  intros m n.
  rewrite about_matrix_exponentiation_left.
  apply about_matrix_exponentiation_right.
Qed.  


(* Transposition of matrix *)

Definition matrix_transposition (m : matrix22) : matrix22 :=
  match m with
    | Matrix22 a00 a01 a10 a11 
      => Matrix22 a00 a10 a01 a11
  end.

Lemma unfold_matrix_transposition :
  forall m : matrix22,
    matrix_transposition m = 
      match m with
        | Matrix22 a00 a01 a10 a11 
          => Matrix22 a00 a10 a01 a11
      end.
Proof.
  unfold matrix_transposition.
  reflexivity.
Qed.


(* Transposition of a matrix test
  
       T
  |1 2|  =  |1  3|
  |3 4|  =  |2  4|   *)

Compute matrix_transposition matrix_1.
 
(* Matrix22 1 3 2 4
    : matrix22       *)


(* Properties about matrix transposition *)

Lemma matrix_identity_is_symmetric :
  matrix_transposition matrix_identity = 
  matrix_identity.
Proof.
  rewrite unfold_matrix_transposition.
  rewrite unfold_matrix_identity.
  reflexivity.
Qed.

Lemma matrix_transposition_is_involutive :
  forall m : matrix22,
    matrix_transposition (matrix_transposition m) = m.
Proof.
  intro a.
  rewrite 2 unfold_matrix_transposition.
  destruct a as [a00 a01 a10 a11].
  reflexivity.
Qed.


(* Transposition of a matrix product 

   When you transpose a product you
   get the product of the transposed
   matrices in reverse order *)

Proposition transposition_of_a_product :
  forall a b : matrix22,
    matrix_transposition (matrix_multiplication a b) =
    matrix_multiplication (matrix_transposition b) (matrix_transposition a). 
Proof.
  intros a b.
  destruct a as [a00 a01 a10 a11].
  destruct b as [b00 b01 b10 b11].
  rewrite 3 unfold_matrix_transposition.
  rewrite 2 unfold_matrix_multiplication.
  rewrite (mult_comm a00).
  rewrite (mult_comm a01).
  rewrite (mult_comm a10).
  rewrite (mult_comm a11).
  rewrite (mult_comm b01).
  rewrite (mult_comm b11).
  rewrite (mult_comm b01).
  rewrite (mult_comm b11).
  reflexivity.
Qed.


(* Transposition and exponentiation commutes

   Proposition 38 in dProgSprog notes *)

Theorem matrix_transposition_and_exponentiation_commutes :
  forall (m : matrix22) (n : nat),
    matrix_transposition (matrix_exponentiation m n) =
    matrix_exponentiation (matrix_transposition m) n.
Proof.
  intros m n.
  induction n as [ | n' IHn'].
  rewrite 2 unfold_matrix_exponentiation_bc.
  rewrite matrix_identity_is_symmetric.
  reflexivity.
  
  destruct m as [m00 m01 m10 m11].
  rewrite (unfold_matrix_exponentiation_ic (matrix_transposition (Matrix22 m00 m01 m10 m11))).
  rewrite <- IHn'.
  rewrite <- transposition_of_a_product.
  rewrite about_matrix_exponentiation_left.
  reflexivity.
Qed.


(* Determinant of 2x2 matrix *)

Definition matrix_determinant (m : matrix22) : nat :=
  match m with 
    | Matrix22 a00 a01 a10 a11 
      => a00 * a11 - a01 * a10
  end.

Lemma unfold_matrix_determinant :
  forall m : matrix22,
    matrix_determinant m =   
    match m with 
      | Matrix22 a00 a01 a10 a11 
        => a00 * a11 - a01 * a10
    end.
Proof.
  unfold matrix_determinant.
  reflexivity.
Qed.

Compute matrix_determinant (Matrix22 10 4 9 9).
(*  54
    : nat *)


(* Defining the fibonacci matrix to raise to a power *)

Definition matrix_fib := Matrix22 1 1 1 0.

Lemma unfold_matrix_fib :
  matrix_fib = Matrix22 1 1 1 0.
Proof.
  unfold matrix_fib.
  reflexivity.
Qed.


(* Matrix exponentiation and fibonacci 

   Showing the beautiful relation between
   matrix exponentiation of the matrix_fib
   and the fibonacci sequence *)

Theorem matrix_exponentiation_and_fibonacci :
  forall (fib : nat -> nat),
    specification_of_fibonacci fib ->
    forall n : nat,
      (matrix_exponentiation matrix_fib (S n)) = Matrix22 (fib (S (S n))) (fib (S n)) (fib (S n)) (fib n).
Proof.
  intro fib.
  intro H_fib.
  destruct H_fib as [H_fib_bc0 [H_fib_bc1 H_fib_ic]].
  intro n.
  induction n as [ | n' IHn'].
  rewrite H_fib_ic.
  rewrite H_fib_bc0.
  rewrite H_fib_bc1.
  rewrite plus_0_r.
  rewrite unfold_matrix_exponentiation_ic.
  rewrite matrix_identity_is_neutral_on_the_left.
  reflexivity.
  
  rewrite unfold_matrix_exponentiation_ic.
  rewrite unfold_matrix_multiplication.
  rewrite IHn'.
  rewrite unfold_matrix_fib.
  rewrite 3 mult_1_r.
  rewrite 2 mult_0_r.
  rewrite 2 plus_0_r.
  rewrite <- 2 H_fib_ic.
  reflexivity.
Qed.


(* Matrix implementation of fibonacci 

   New implementation of the Fibonacci function 
   maybe also be a bit more efficient *)

Fixpoint fib_v3 (n : nat) : nat :=
  match (matrix_exponentiation (Matrix22 1 1 1 0) n) with
    | Matrix22 _ a01 _ _ => a01
  end.

Compute map fib_v3 (0 :: 1 :: 2 :: 3 :: 4 :: 5 :: 6 :: 7 :: nil).
(*                  0 :: 1 :: 1 :: 2 :: 3 :: 5 :: 8 :: 13 :: nil
                    : list nat *)


Lemma unfold_fib_v3_bc :
  fib_v3 0 = 
  match (matrix_exponentiation matrix_fib 0) with
    | Matrix22 _ a01 _ _ => a01
  end.
Proof.
  unfold fib_v3.
  reflexivity.
Qed.

Lemma fib_v3_of_0 :
  fib_v3 0 = 0.
Proof.
  rewrite unfold_fib_v3_bc.
  rewrite unfold_matrix_exponentiation_bc.
  rewrite unfold_matrix_identity.
  reflexivity.
Qed.

Lemma unfold_fib_v3_ic :
  forall n : nat,
    fib_v3 (S n) =
    match (matrix_exponentiation matrix_fib (S n)) with
      | Matrix22 _ a01 _ _ => a01
    end.
Proof.
  unfold fib_v3.
  reflexivity.
Qed.


(* Fibonacci function in direct style

   Implementation from 
   'fibonacci-with-some-solutions.v' *)

Fixpoint fib_v1 (n : nat) : nat :=
  match n with
    | 0 => 0
    | S n' => match n' with
                | 0 => 1
                | S n'' => fib_v1 n' + fib_v1 n''
              end
  end.

Lemma unfold_fib_v1_base_case_0 :
  fib_v1 0 = 0.
Proof.
  unfold fib_v1.
  reflexivity.
Qed.

Lemma unfold_fib_v1_base_case_1 :
  fib_v1 1 = 1.
Proof.
  unfold fib_v1.
  reflexivity.
Qed.

Lemma unfold_fib_v1_induction_case :
  forall n'' : nat,
    fib_v1 (S (S n'')) = fib_v1 (S n'') + fib_v1 n''.
Proof.
  intro n''.
  unfold fib_v1; fold fib_v1.
  reflexivity.
Qed.


Theorem fib_v1_fits_the_specification_of_fibonacci :
  specification_of_fibonacci fib_v1.
Proof.
  unfold specification_of_fibonacci.
  split.
  apply unfold_fib_v1_base_case_0.
  split.
  apply unfold_fib_v1_base_case_1.
  apply unfold_fib_v1_induction_case.
Qed.


(* fib_v1 and fib_v3 are functionally equal

   For any natural number n the output
   of fib_v1 and fib_v3 are the same *)

Proposition fib_v1_and_fib_v3_are_functionally_equal :
  forall n : nat,
    fib_v3 n = fib_v1 n.
Proof.
  intro n.
  induction n as [ | | n' IHn' IHSn'] using nat_ind2.
  rewrite fib_v3_of_0.
  rewrite unfold_fib_v1_base_case_0.
  reflexivity.
  
  rewrite unfold_fib_v3_ic.
  rewrite unfold_fib_v1_base_case_1.
  rewrite unfold_matrix_exponentiation_ic.
  rewrite unfold_matrix_exponentiation_bc.
  rewrite matrix_identity_is_neutral_on_the_left.
  rewrite unfold_matrix_fib.
  reflexivity.

  rewrite unfold_fib_v3_ic.
  rewrite (matrix_exponentiation_and_fibonacci fib_v1 fib_v1_fits_the_specification_of_fibonacci).
  reflexivity.
Qed.


(* fib_v3 satisfies the specification of Fibonacci 

   Since fib_v1 and fib_v3 are functionally equal
   it is straight forward to show that fib_v3 satisfies the 
   specification since it is already shown that
   fib_v1 satisfies the specification. *)

Theorem fib_v3_satisfies_the_specification_of_fibonacci :
  specification_of_fibonacci fib_v3.
Proof.
  unfold specification_of_fibonacci.
  rewrite 2 fib_v1_and_fib_v3_are_functionally_equal.
  destruct fib_v1_fits_the_specification_of_fibonacci 
    as [fib_v1_bc0 [fib_v1_bc1 fib_v1_ic]].
  split.
  apply fib_v1_bc0.
  split.
  apply fib_v1_bc1.
  intro n.
  rewrite 3 fib_v1_and_fib_v3_are_functionally_equal.
  apply fib_v1_ic.
Qed.
  

(* Cassini's identity with matrices 

   This implementation uses a fibonacci
   function to create the fibonacci matrix.
   And afterwards the definition of the
   determinant ensures an expression
   where Cassini_s_identity_for_even_numbers
   can be used. *)


Theorem Cassini_and_matrices_even :
  forall (fib : nat -> nat) (n : nat),
    specification_of_fibonacci fib ->
    matrix_determinant (matrix_exponentiation matrix_fib (2 * (S n))) = 1.
Proof.
  intros fib n.
  intro H_fib.
  assert (H_tmp := H_fib).
  destruct H_fib as [H_fib_bc0 [H_fib_bc1 H_fib_ic]].

  rewrite unfold_matrix_fib.
  rewrite mult_succ_l.
  rewrite mult_1_l.
  rewrite plus_Sn_m.
  rewrite <- plus_n_Sm.
  rewrite (matrix_exponentiation_and_fibonacci fib H_tmp).
  rewrite <- plus_Sn_m.
  rewrite plus_n_Sm.
  rewrite (plus_Sn_m n n).
  rewrite 2 plus_2_mult.
  rewrite unfold_matrix_determinant.
  rewrite <- (Cassini_s_identity_for_even_numbers fib H_tmp n).
  rewrite unfold_square.
  rewrite <- minus_Sn_m.
  rewrite minus_diag.
  reflexivity.
  
  reflexivity.
Qed.


Theorem Cassini_and_matrices_odd :
  forall (fib : nat -> nat) (n : nat),
    specification_of_fibonacci fib ->
   S (S (matrix_determinant (matrix_exponentiation matrix_fib (S (2 * n))))) = 1.
Proof.
  intros fib n.
  intro H_fib.
  assert (H_tmp := H_fib).
  destruct H_fib as [H_fib_bc0 [H_fib_bc1 H_fib_ic]].

  rewrite unfold_matrix_fib.
  rewrite mult_succ_l.
  rewrite mult_1_l.
  rewrite (matrix_exponentiation_and_fibonacci fib H_tmp).
  rewrite <- plus_Sn_m.
  rewrite plus_n_Sm.
  rewrite 2 plus_2_mult.
  rewrite plus_Sn_m.
  rewrite plus_2_mult.
  rewrite unfold_matrix_determinant.
  rewrite <- fibonacci.unfold_square.
  rewrite (Cassini_s_identity_for_odd_numbers fib H_tmp n).
  rewrite minus_Sn_m.
  rewrite minus_diag.
  reflexivity.
  (* Will not appear in the report *)
  Abort.

(* End of 'matrix.v' *)

