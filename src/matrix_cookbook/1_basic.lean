import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.trace
import data.real.nnreal
import topology.metric_space.basic
import data.matrix.notation
import ring_theory.power_series.basic

/-! # Basics -/

variables {ι : Type*} {R : Type*} {m n p : Type*}
variables [fintype m] [fintype n] [fintype p]
variables [decidable_eq m] [decidable_eq n] [decidable_eq p]

namespace matrix_cookbook

open_locale matrix big_operators filter topological_space
open matrix

-- anyone looking at the cookbook likely only cares about fields anyway!
variables [field R]

lemma eq_1 {A : matrix m m R} {B : matrix m m R} : (A * B)⁻¹ = B⁻¹ * A⁻¹ := matrix.mul_inv_rev _ _
lemma eq_2 {l : list (matrix m m R)} : l.prod⁻¹ = (l.reverse.map has_inv.inv).prod := sorry
lemma eq_3 {A : matrix m m R} : Aᵀ⁻¹ = A⁻¹ᵀ := (transpose_nonsing_inv _ sorry).symm
lemma eq_4 {A B : matrix m n R} : (A + B)ᵀ = Aᵀ + Bᵀ := transpose_add _ _
lemma eq_5 {A : matrix m n R} {B : matrix n p R} : (A ⬝ B)ᵀ = Bᵀ ⬝ Aᵀ := transpose_mul _ _
lemma eq_6 {l : list (matrix m m R)} : l.prodᵀ = (l.reverse.map transpose).prod := sorry
lemma eq_7 [star_ring R] {A : matrix m m R} : Aᴴ⁻¹ = A⁻¹ᴴ := sorry
lemma eq_8 [star_ring R] {A B : matrix m n R} : (A + B)ᴴ = Aᴴ + Bᴴ := conj_transpose_add _ _
lemma eq_9 [star_ring R] {A : matrix m n R} {B : matrix n p R} : (A ⬝ B)ᴴ = Bᴴ ⬝ Aᴴ := conj_transpose_mul _ _
lemma eq_10 [star_ring R] {l : list (matrix m m R)} : l.prodᴴ = (l.reverse.map conj_transpose).prod := sorry

/-! ### Trace -/
section
local notation `Tr` := matrix.trace _ R R

lemma eq_11 {A : matrix m m R} : Tr A = ∑ i, A i i := matrix.trace_apply _
lemma eq_12 {A : matrix m m R} (eigvals : m → R) : Tr A = ∑ i, eigvals i := sorry
lemma eq_13 {A : matrix m m R} : Tr A = Tr Aᵀ := (matrix.trace_transpose _).symm
lemma eq_14 {A : matrix m n R} {B : matrix n m R} : Tr (A ⬝ B) = Tr (B ⬝ A) := matrix.trace_mul_comm _ _
lemma eq_15 {A B : matrix m m R} : Tr (A + B) = Tr A + Tr B := (matrix.trace _ _ _).map_add _ _
lemma eq_16 {A : matrix m n R} {B : matrix n p R} {C : matrix p m R} :
  Tr (A ⬝ B ⬝ C) = Tr (B ⬝ C ⬝ A) := sorry
lemma eq_17 {a : m → R} : dot_product a a = Tr (col a ⬝ row a) := sorry

end

/-! ### Determinant -/

lemma eq_18 {A : matrix m m R} (eigvals : m → R) : det A = ∏ i, eigvals i := sorry
lemma eq_19 (c : R) {A : matrix m m R} : det (c • A) = c ^ fintype.card m * det A := det_smul _ _
lemma eq_20 {A : matrix m m R} : det (Aᵀ) = det A := det_transpose _
lemma eq_21 {A B : matrix m m R} : det (A * B) = det A * det B := det_mul _ _
lemma eq_22 {A : matrix m m R} : det (A⁻¹) = (det A)⁻¹ := sorry
lemma eq_23 {A : matrix m m R} (k : ℕ) : det (A ^ k) = (det A) ^ k := det_pow _ _
lemma eq_24 {u v : m → R} : det (1 + col u ⬝ row v) = 1 + dot_product u v := sorry
section
local notation `Tr` := matrix.trace _ R R
lemma eq_25 {A : matrix (fin 2) (fin 2) R} : det (1 + A) = 1 + det A + Tr A := by { simp [det_fin_two, fin.sum_univ_succ], ring }
lemma eq_26 {A : matrix (fin 3) (fin 3) R} :
  det (1 + A) = 1 + det A + Tr A + 1/2*Tr A^2 - 1/2*Tr (A^2) := sorry
lemma eq_27 {A : matrix (fin 4) (fin 4) R} :
  det (1 + A) = 1 + det A + Tr A + 1/2*Tr A^2 - 1/2*Tr (A^2) + 1/6*Tr A^3 - 1/2*Tr A * Tr (A^2) + 1/3 * Tr (A^3) := sorry
end
/-! Note: it is likely that eq (28) is just wrong in the source material! -/
section
local notation `Tr` := matrix.trace _ ℝ ℝ
-- TODO: is this statement correct?
lemma eq_28 {A : matrix n n ℝ} :
  (λ ε : nnreal, det (1 + ε • A)) =ᶠ[filter.at_bot] (λ ε, 1 + det A + ε * Tr A + 1/2 * ε^2 * Tr(A)^2 - 1/2 * ε^2 * Tr (A^2)) := sorry
end
section
local notation `Tr` := matrix.trace _ R _
-- TODO: or is this statement correct?
lemma eq_28' {A : matrix n n R} :
  let ε : power_series R := power_series.X,
      A : matrix n n (power_series R) := A.map (power_series.C _) in
  (det (1 + ε • A)).trunc 2 = (1 + det A + ε • Tr A + (1/2 : R) •  ε^2 * Tr(A)^2 - (1/2 : R) • ε^2 * Tr (A^2)).trunc 2 := sorry
end

/-! ### The special case 2×2-/
section
local notation `Tr` := matrix.trace _ R R

lemma eq_29 {A : matrix (fin 2) (fin 2) R} : det A = A 0 0 * A 1 1 - A 0 1 * A 1 0 := det_fin_two _
lemma eq_30 {A : matrix (fin 2) (fin 2) R} : Tr A = A 0 0 + A 1 1 := by simp [fin.sum_univ_succ]  -- TODO: add a lemma in mathlib

/-! Note: there are some non-numbered eigenvalue things here -/

lemma eq_31 {A : matrix (fin 2) (fin 2) R} : A⁻¹ = (det A)⁻¹ • ![![A 1 1, -A 0 1], ![-A 1 0, A 0 0]] := sorry

end

end matrix_cookbook
