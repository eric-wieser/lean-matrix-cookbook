/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import data.matrix.basic
import data.complex.basic
import linear_algebra.matrix.determinant
import linear_algebra.matrix.nonsingular_inverse
import data.matrix.notation

import matrix_cookbook.for_mathlib.data.matrix

/-! # Adjugate Matrix : Extra Lemmas -/

open matrix
open_locale matrix big_operators

variables {R: Type*}[comm_ring R]

def cofactor {n : ℕ} (A : matrix (fin n.succ) (fin n.succ) R) (i j: fin n.succ)  :=
  (-1)^(i + j : ℕ) * det (A.submatrix i.succ_above j.succ_above)

/- Lemma should state
lemma eq_146 (n : ℕ) (A : matrix (fin n.succ) (fin n.succ) ℂ) (i j) :
  adjugate A j i = cofactor A i j := 
-/
lemma adjugate_eq_cofactor_transpose {n : ℕ} (A : matrix (fin n.succ) (fin n.succ) R) 
  (i j) : adjugate A j i = cofactor A i j := 
begin
  rw adjugate, dsimp,
  rw cramer_transpose_apply,
  rw det_succ_row _ i,
  conv_lhs { apply_congr, skip, rw update_row_apply, },
  simp only [eq_self_iff_true, if_true],
  conv_lhs {apply_congr, skip, rw pi.single_apply j (1:R) x, 
  rw mul_ite, rw ite_mul, rw mul_zero, rw zero_mul, },
  simp only [mul_one, finset.sum_ite_eq', finset.mem_univ, if_true, 
    neg_one_pow_mul_eq_zero_iff],
  rw cofactor,
  rw submatrix_update_row_succ_above,
end

