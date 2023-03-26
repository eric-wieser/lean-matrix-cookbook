import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.trace
import data.real.nnreal
import topology.metric_space.basic
import data.matrix.notation
import ring_theory.power_series.basic
import tactic.norm_fin

/-! # Basics -/

variables {ι : Type*} {R : Type*} {m n p : Type*}
variables [fintype m] [fintype n] [fintype p]
variables [decidable_eq m] [decidable_eq n] [decidable_eq p]

namespace matrix_cookbook

open_locale matrix big_operators filter topology
open matrix

-- anyone looking at the cookbook likely only cares about fields anyway!
variables [field R]

lemma eq_1 {A : matrix m m R} {B : matrix m m R} : (A * B)⁻¹ = B⁻¹ * A⁻¹ := matrix.mul_inv_rev _ _
lemma eq_2 {l : list (matrix m m R)} : l.prod⁻¹ = (l.reverse.map has_inv.inv).prod := matrix.list_prod_inv_reverse _
lemma eq_3 {A : matrix m m R} : Aᵀ⁻¹ = A⁻¹ᵀ := (transpose_nonsing_inv _).symm
lemma eq_4 {A B : matrix m n R} : (A + B)ᵀ = Aᵀ + Bᵀ := transpose_add _ _
lemma eq_5 {A : matrix m n R} {B : matrix n p R} : (A ⬝ B)ᵀ = Bᵀ ⬝ Aᵀ := transpose_mul _ _
lemma eq_6 {l : list (matrix m m R)} : l.prodᵀ = (l.map transpose).reverse.prod := matrix.transpose_list_prod _
lemma eq_7 [star_ring R] {A : matrix m m R} : Aᴴ⁻¹ = A⁻¹ᴴ := (conj_transpose_nonsing_inv _).symm
lemma eq_8 [star_ring R] {A B : matrix m n R} : (A + B)ᴴ = Aᴴ + Bᴴ := conj_transpose_add _ _
lemma eq_9 [star_ring R] {A : matrix m n R} {B : matrix n p R} : (A ⬝ B)ᴴ = Bᴴ ⬝ Aᴴ := conj_transpose_mul _ _
lemma eq_10 [star_ring R] {l : list (matrix m m R)} : l.prodᴴ = (l.map conj_transpose).reverse.prod := matrix.conj_transpose_list_prod _

/-! ### Trace -/
section

lemma eq_11 {A : matrix m m R} : trace A = ∑ i, A i i := rfl
lemma eq_12 {A : matrix m m R} (eigvals : m → R) : trace A = ∑ i, eigvals i := sorry
lemma eq_13 {A : matrix m m R} : trace A = trace Aᵀ := (matrix.trace_transpose _).symm
lemma eq_14 {A : matrix m n R} {B : matrix n m R} : trace (A ⬝ B) = trace (B ⬝ A) := matrix.trace_mul_comm _ _
lemma eq_15 {A B : matrix m m R} : trace (A + B) = trace A + trace B := trace_add _ _
lemma eq_16 {A : matrix m n R} {B : matrix n p R} {C : matrix p m R} :
  trace (A ⬝ B ⬝ C) = trace (B ⬝ C ⬝ A) := (matrix.trace_mul_cycle B C A).symm
lemma eq_17 {a : m → R} : dot_product a a = trace (col a ⬝ row a) := (matrix.trace_col_mul_row _ _).symm

end

/-! ### Determinant -/

-- `matrix.is_hermitian.det_eq_prod_eigenvalues` is close, but needs `A` to be hermitian which is too strong
lemma eq_18 {A : matrix m m R} (eigvals : m → R) : det A = ∏ i, eigvals i := sorry
lemma eq_19 (c : R) {A : matrix m m R} : det (c • A) = c ^ fintype.card m * det A := det_smul _ _
lemma eq_20 {A : matrix m m R} : det (Aᵀ) = det A := det_transpose _
lemma eq_21 {A B : matrix m m R} : det (A * B) = det A * det B := det_mul _ _
lemma eq_22 {A : matrix m m R} : det (A⁻¹) = (det A)⁻¹ := (det_nonsing_inv _).trans (ring.inverse_eq_inv _)
lemma eq_23 {A : matrix m m R} (k : ℕ) : det (A ^ k) = (det A) ^ k := det_pow _ _
lemma eq_24 {u v : m → R} : det (1 + col u ⬝ row v) = 1 + dot_product u v :=
by rw [det_one_add_col_mul_row u v, dot_product_comm]
lemma eq_25 {A : matrix (fin 2) (fin 2) R} : det (1 + A) = 1 + det A + trace A := 
by { simp [det_fin_two, trace_fin_two], ring }
lemma eq_26 {A : matrix (fin 3) (fin 3) R} [invertible (2 : R)] :
  det (1 + A) = 1 + det A + trace A + ⅟2*trace A^2 - ⅟2*trace (A^2) :=
begin
  apply mul_left_cancel₀ (is_unit_of_invertible (2 : R)).ne_zero,
  simp only [det_fin_three, trace_fin_three, pow_two, matrix.mul_eq_mul, matrix.mul_apply, fin.sum_univ_succ,
    matrix.one_apply],
  dsimp,
  simp only [mul_add, mul_sub, mul_inv_of_self_assoc],
  simp_rw matrix.one_apply,
  simp,
  norm_num,
  ring,
  -- ring,
end
lemma eq_27 {A : matrix (fin 4) (fin 4) R} :
  det (1 + A) = 1 + det A + trace A + 1/2*trace A^2 - 1/2*trace (A^2) + 1/6*trace A^3 - 1/2*trace A * trace (A^2) + 1/3 * trace (A^3) := sorry

/-! Note: it is likely that eq (28) is just wrong in the source material! -/

-- TODO: is this statement correct?
lemma eq_28 {A : matrix n n ℝ} :
  (λ ε : nnreal, det (1 + ε • A)) =ᶠ[filter.at_bot] (λ ε, 1 + det A + ε * trace A + 1/2 * ε^2 * trace(A)^2 - 1/2 * ε^2 * trace (A^2)) := sorry

-- TODO: or is this statement correct?
lemma eq_28' {A : matrix n n R} :
  let ε : power_series R := power_series.X,
      A : matrix n n (power_series R) := A.map (power_series.C _) in
  (det (1 + ε • A)).trunc 2 = (1 + det A + ε • trace A + (1/2 : R) •  ε^2 * trace(A)^2 - (1/2 : R) • ε^2 * trace (A^2)).trunc 2 := sorry


/-! ### The special case 2×2-/
section

lemma eq_29 {A : matrix (fin 2) (fin 2) R} : det A = A 0 0 * A 1 1 - A 0 1 * A 1 0 := det_fin_two _
lemma eq_30 {A : matrix (fin 2) (fin 2) R} : trace A = A 0 0 + A 1 1 := trace_fin_two _

/-! Note: there are some non-numbered eigenvalue things here -/

lemma eq_31 {A : matrix (fin 2) (fin 2) R} : A⁻¹ = (det A)⁻¹ • !![A 1 1, -A 0 1; -A 1 0, A 0 0] :=
by rw [inv_def, adjugate_fin_two, ring.inverse_eq_inv]

end

end matrix_cookbook
