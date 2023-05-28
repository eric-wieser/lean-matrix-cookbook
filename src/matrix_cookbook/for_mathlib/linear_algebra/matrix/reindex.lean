/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.reindex

/-! # Matrix Reindex: Lemmas of equivalence -/

open matrix
open_locale matrix big_operators

variables {m n: Type*}[fintype m][fintype n][decidable_eq m][decidable_eq n]
variables {o p: Type*}[fintype o][fintype p][decidable_eq o][decidable_eq p]
variables {R: Type*}[field R]

lemma reindex_equiv_eq_if_matrix_eq (e₁ : m ≃ o) (e₂: n ≃ p) (A B: matrix m n R) : 
  (reindex e₁ e₂ A = reindex e₁ e₂ B) → A = B :=
begin
  intro h,
  rw ← matrix.ext_iff at h,
  funext r s,
  specialize h (e₁ r) (e₂ s),
  simp only [reindex_apply, submatrix_apply, equiv.symm_apply_apply] at h,
  exact h,
end

lemma matrix_eq_if_reindex_equiv (e₁ : m ≃ o) (e₂: n ≃ p) (A B: matrix m n R) : 
  A = B → (reindex e₁ e₂ A = reindex e₁ e₂ B) :=
begin
  rw [← matrix.ext_iff, reindex_apply, reindex_apply],
  intro h,
  funext r s,
  apply h,
end

lemma reindex_equiv_eq_iff_matrix_eq (e₁ e₂ : n ≃ m) (A B: matrix n n R) : 
  (reindex e₁ e₂ A = reindex e₁ e₂ B) ↔ A = B :=
⟨ reindex_equiv_eq_if_matrix_eq _ _ _ _, matrix_eq_if_reindex_equiv _ _ _ _⟩
