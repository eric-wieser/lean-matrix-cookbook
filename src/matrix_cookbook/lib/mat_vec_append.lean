/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.reindex
import matrix_cookbook.for_mathlib.linear_algebra.matrix.reindex

/-! # Support Definitions and Lemmas for Rank one Updates by concatenation-/
namespace matrix_cookbook

open matrix
open_locale matrix big_operators

variables {m n: Type*}[fintype m][fintype n][decidable_eq m][decidable_eq n]
variables {R: Type*}[field R]

variable X : matrix (m ⊕ unit) m R
variable v : matrix (m ⊕ unit) unit R
def append_mat_vec := of (λ i, sum.elim (X i) (v i))

lemma rank_one_update_transpose_mul_self :
  (append_mat_vec X v)ᵀ ⬝ append_mat_vec X v =
    from_blocks (Xᵀ ⬝ X) (Xᵀ ⬝ v) (vᵀ ⬝ X) (vᵀ ⬝ v) :=
begin
  funext r s,
  rw append_mat_vec,
  cases s, cases r, work_on_goal 3 {cases r},
  all_goals 
  { simp only [mul_apply, transpose_apply, of_apply, sum.elim_inl, sum.elim_inr,
    from_blocks_apply₁₁, from_blocks_apply₁₂, from_blocks_apply₂₁, from_blocks_apply₂₂, 
    mul_apply, transpose_apply],},
end

lemma fin_one_mul_eq_smul {A: matrix unit m R} {q: matrix unit unit R}:
  (q () ()) • A = q ⬝ A := 
begin
  funext r s,
  simp only [pi.smul_apply, algebra.id.smul_eq_mul, mul_apply, 
    fintype.univ_of_subsingleton, finset.sum_singleton],
  congr,
end

end matrix_cookbook
