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

variables {R : Type*} [comm_ring R]

lemma adjugate_eq_det_submatrix {n : ℕ} (A : matrix (fin n.succ) (fin n.succ) R) (i j) :
  adjugate A i j = (-1)^(j + i : ℕ) * det (A.submatrix j.succ_above i.succ_above) := 
begin
  simp_rw [adjugate_apply, det_succ_row _ j, update_row_self, submatrix_update_row_succ_above],
  rw [fintype.sum_eq_single i (λ h hjk, _), pi.single_eq_same, mul_one],
  rw [pi.single_eq_of_ne hjk, mul_zero, zero_mul],
end

lemma det_eq_sum_mul_adjugate_row {n : Type*} [decidable_eq n] [fintype n]
  (A : matrix n n R) (i : n) :
  det A = ∑ j : n, A i j * adjugate A j i := 
begin
  haveI : nonempty n := ⟨i⟩,
  obtain ⟨n', hn'⟩ := nat.exists_eq_succ_of_ne_zero (fintype.card_ne_zero : fintype.card n ≠ 0),
  obtain ⟨e⟩ := fintype.trunc_equiv_fin_of_card_eq hn',
  let A' := reindex e e A,
  suffices : det A' = ∑ j : fin n'.succ, A' (e i) j * adjugate A' j (e i),
  { simp_rw [A', det_reindex_self, adjugate_reindex, reindex_apply, submatrix_apply, ←e.sum_comp,
      equiv.symm_apply_apply] at this,
    exact this },
  rw det_succ_row A' (e i),
  simp_rw [mul_assoc, mul_left_comm _ (A' _ _), ←adjugate_eq_det_submatrix],
end
