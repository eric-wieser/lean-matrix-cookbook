/-
Copyright (c) 2023 Mohanad Ahmed, Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed, Eric Wieser
-/
import linear_algebra.matrix.trace
import linear_algebra.matrix.determinant
import data.matrix.notation
import data.fintype.big_operators
import tactic.ring
import tactic.norm_fin
import data.is_R_or_C.basic
import algebra.char_p.basic
import matrix_cookbook.for_mathlib.data.matrix

/-!
#  Traces and Determinants of 1st, 2nd and 3rd Powers of 4x4 Matrices

This file contains lemmas in rather verbose form of matrix fin 4 fin 4 R.

These are used to prove equation 27 in the matrix cookbook. 

The results are all field results. The last one `eq_27_before_last` which
involves multiplication and division by the numbers 2, 3 and 6 imposes more
requirement, which I satsified by requiring a field with characteristic zero.

-/

open_locale matrix big_operators
open matrix

variables {R : Type*} [comm_ring R]

lemma trace_pow_two_fin_four (A : matrix (fin 4) (fin 4) R) :
  trace (A^2) = 
    A 0 0^2 + A 1 1^2 + A 2 2^2 + A 3 3^2 + 
    2*A 0 1*A 1 0 + 2*A 0 2*A 2 0 + 2*A 0 3*A 3 0 + 
    2*A 1 2*A 2 1 + 2*A 1 3*A 3 1 + 2*A 2 3*A 3 2 := 
begin
  simp_rw [matrix.trace_fin_four, pow_two, mul_eq_mul, mul_apply, fin.sum_univ_four],
  ring,
end

lemma trace_pow_three_fin_four (A : matrix (fin 4) (fin 4) R) :
  trace (A^3) = 
    A 0 0*(A 0 0^2 + A 0 1*A 1 0 + A 0 2*A 2 0 + A 0 3*A 3 0) + 
    A 1 1*(A 1 1^2 + A 0 1*A 1 0 + A 1 2*A 2 1 + A 1 3*A 3 1) + 
    A 2 2*(A 2 2^2 + A 0 2*A 2 0 + A 1 2*A 2 1 + A 2 3*A 3 2) + 
    A 3 3*(A 3 3^2 + A 0 3*A 3 0 + A 1 3*A 3 1 + A 2 3*A 3 2) + 
    A 1 0*(A 0 0*A 0 1 + A 0 1*A 1 1 + A 0 2*A 2 1 + A 0 3*A 3 1) + 
    A 2 0*(A 0 0*A 0 2 + A 0 1*A 1 2 + A 0 2*A 2 2 + A 0 3*A 3 2) + 
    A 0 1*(A 0 0*A 1 0 + A 1 0*A 1 1 + A 1 2*A 2 0 + A 1 3*A 3 0) + 
    A 3 0*(A 0 0*A 0 3 + A 0 1*A 1 3 + A 0 2*A 2 3 + A 0 3*A 3 3) + 
    A 2 1*(A 0 2*A 1 0 + A 1 1*A 1 2 + A 1 2*A 2 2 + A 1 3*A 3 2) + 
    A 0 2*(A 0 0*A 2 0 + A 1 0*A 2 1 + A 2 0*A 2 2 + A 2 3*A 3 0) + 
    A 3 1*(A 0 3*A 1 0 + A 1 1*A 1 3 + A 1 2*A 2 3 + A 1 3*A 3 3) + 
    A 1 2*(A 0 1*A 2 0 + A 1 1*A 2 1 + A 2 1*A 2 2 + A 2 3*A 3 1) + 
    A 0 3*(A 0 0*A 3 0 + A 1 0*A 3 1 + A 2 0*A 3 2 + A 3 0*A 3 3) + 
    A 3 2*(A 0 3*A 2 0 + A 1 3*A 2 1 + A 2 2*A 2 3 + A 2 3*A 3 3) + 
    A 1 3*(A 0 1*A 3 0 + A 1 1*A 3 1 + A 2 1*A 3 2 + A 3 1*A 3 3) + 
    A 2 3*(A 0 2*A 3 0 + A 1 2*A 3 1 + A 2 2*A 3 2 + A 3 2*A 3 3) := 
begin
  simp_rw [matrix.trace_fin_four, pow_three, mul_eq_mul, mul_apply, fin.sum_univ_four],
  ring,
end

lemma det_one_add_fin_four (A : matrix (fin 4) (fin 4) R) :
  (1 + A).det = 
    A 0 0 + A 1 1 + A 2 2 + A 3 3 + 
    A 0 0*A 1 1 - A 0 1*A 1 0 + A 0 0*A 2 2 - A 0 2*A 2 0 + 
    A 0 0*A 3 3 - A 0 3*A 3 0 + A 1 1*A 2 2 - A 1 2*A 2 1 + 
    A 1 1*A 3 3 - A 1 3*A 3 1 + A 2 2*A 3 3 - A 2 3*A 3 2 + 
    A 0 0*A 1 1*A 2 2 - A 0 0*A 1 2*A 2 1 - A 0 1*A 1 0*A 2 2 + A 0 1*A 1 2*A 2 0 + 
    A 0 2*A 1 0*A 2 1 - A 0 2*A 1 1*A 2 0 + A 0 0*A 1 1*A 3 3 - A 0 0*A 1 3*A 3 1 -
    A 0 1*A 1 0*A 3 3 + A 0 1*A 1 3*A 3 0 + A 0 3*A 1 0*A 3 1 - A 0 3*A 1 1*A 3 0 + 
    A 0 0*A 2 2*A 3 3 - A 0 0*A 2 3*A 3 2 - A 0 2*A 2 0*A 3 3 + A 0 2*A 2 3*A 3 0 +
    A 0 3*A 2 0*A 3 2 - A 0 3*A 2 2*A 3 0 + A 1 1*A 2 2*A 3 3 - A 1 1*A 2 3*A 3 2 - 
    A 1 2*A 2 1*A 3 3 + A 1 2*A 2 3*A 3 1 + A 1 3*A 2 1*A 3 2 - A 1 3*A 2 2*A 3 1 + 
    A 0 0*A 1 1*A 2 2*A 3 3 - A 0 0*A 1 1*A 2 3*A 3 2 - A 0 0*A 1 2*A 2 1*A 3 3 + 
    A 0 0*A 1 2*A 2 3*A 3 1 + A 0 0*A 1 3*A 2 1*A 3 2 - A 0 0*A 1 3*A 2 2*A 3 1 - 
    A 0 1*A 1 0*A 2 2*A 3 3 + A 0 1*A 1 0*A 2 3*A 3 2 + A 0 1*A 1 2*A 2 0*A 3 3 - 
    A 0 1*A 1 2*A 2 3*A 3 0 - A 0 1*A 1 3*A 2 0*A 3 2 + A 0 1*A 1 3*A 2 2*A 3 0 + 
    A 0 2*A 1 0*A 2 1*A 3 3 - A 0 2*A 1 0*A 2 3*A 3 1 - A 0 2*A 1 1*A 2 0*A 3 3 + 
    A 0 2*A 1 1*A 2 3*A 3 0 + A 0 2*A 1 3*A 2 0*A 3 1 - A 0 2*A 1 3*A 2 1*A 3 0 - 
    A 0 3*A 1 0*A 2 1*A 3 2 + A 0 3*A 1 0*A 2 2*A 3 1 + A 0 3*A 1 1*A 2 0*A 3 2 - 
    A 0 3*A 1 1*A 2 2*A 3 0 - A 0 3*A 1 2*A 2 0*A 3 1 + A 0 3*A 1 2*A 2 1*A 3 0 + 1 := 
begin
  simp only [det_fin_four, pi.add_apply, one_apply_eq],
  simp only [one_apply_ne] {discharger := `[dec_trivial] },
  ring,
end

lemma sq_trace_fin_four (A : matrix (fin 4) (fin 4) R) :
  (trace A)^2 = 
    A 0 0^2 + A 1 1^2 + A 2 2^2 + A 3 3^2 + 
    2*A 0 0*A 1 1 + 2*A 0 0*A 2 2 + 2*A 0 0*A 3 3 + 
    2*A 1 1*A 2 2 + 2*A 1 1*A 3 3 + 2*A 2 2*A 3 3 :=
begin
  rw [trace_fin_four, pow_two], 
  ring,
end

lemma eq_27_before_last {R} [field R] [char_zero R] (A : matrix (fin 4) (fin 4) R)  :
  det (1 + A) - det A - 1 = trace A + 
    (1/2)*( (trace A)^2 - trace (A^2)) + 
    (1/6)*( (trace A)^3 - 3*trace A * trace (A^2) + 2 * trace (A^3) ) := 
begin
  field_simp,
  rw [det_one_add_fin_four, det_fin_four, trace_pow_three_fin_four, trace_pow_two_fin_four,
    sq_trace_fin_four, trace_fin_four],
  ring,
end

