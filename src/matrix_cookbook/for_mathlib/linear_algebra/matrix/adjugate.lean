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

/-! # Adjugate Matrix : Extra Lemmas -/

open matrix
open_locale matrix big_operators

lemma submatrix_succ_above {α k l} {n : ℕ} {A : matrix (fin n.succ) k α} (v : k → α) {f : l → k} {i} : 
  (A.update_row i v).submatrix i.succ_above f = A.submatrix i.succ_above f := 
begin
  funext r s,
  rw submatrix_apply,
  rw submatrix_apply,
  rw update_row_apply,
  rw if_eq_of_eq_false,
  rw eq_iff_iff, split, apply fin.succ_above_ne, 
  trivial,
end

def cofactor {n : ℕ} (A : matrix (fin n.succ) (fin n.succ) ℂ) (i j: fin n.succ)  :=
  (-1)^(i + j : ℕ) * det (A.submatrix i.succ_above j.succ_above)

/- Lemma should state
lemma eq_146 (n : ℕ) (A : matrix (fin n.succ) (fin n.succ) ℂ) (i j) :
  adjugate A j i = cofactor A i j := 
-/
lemma adjugate_eq_cofactor_transpose {n : ℕ} (A : matrix (fin n.succ) (fin n.succ) ℂ) 
  (i j) : adjugate A j i = cofactor A i j := 
begin
  rw adjugate, dsimp,
  rw cramer_transpose_apply,
  rw det_succ_row _ i,
  conv_lhs { apply_congr, skip, rw update_row_apply, },
  simp only [eq_self_iff_true, if_true],
  conv_lhs {apply_congr, skip, rw pi.single_apply j (1:ℂ) x, 
  rw mul_ite, rw ite_mul, rw mul_zero, rw zero_mul, },
  simp only [mul_one, finset.sum_ite_eq', finset.mem_univ, if_true, 
    neg_one_pow_mul_eq_zero_iff],
  rw cofactor,
  rw submatrix_succ_above,
end

