import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.reindex
import matrix_cookbook.for_mathlib.linear_algebra.matrix.reindex

namespace matrix_cookbook

open matrix
open_locale matrix big_operators

variables {m n: Type*}[fintype m][fintype n][decidable_eq m][decidable_eq n]
variables {R: Type*}[field R]

variable z : ℕ
variable X : matrix (m ⊕ unit) m R
variable v : matrix (m ⊕ unit) unit R
def append_mat_vec := of (λ i, sum.elim (X i) (v i))
-- def e := @fin_sum_fin_equiv z 1

lemma fin_one_mul_eq_smul {A: matrix unit m R} {q: matrix unit unit R}:
  (q () ()) • A = q ⬝ A := 
begin
  funext r s,
  simp only [pi.smul_apply, algebra.id.smul_eq_mul, mul_apply, 
    fintype.univ_of_subsingleton, finset.sum_singleton],
  congr,
end

lemma rank_one_update_transpose_mul_self
  (X : matrix (m ⊕ unit) m R)
  (v : matrix (m ⊕ unit) unit R)
  [invertible (Xᵀ ⬝ X)] :
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

lemma sS11
  (X : matrix (m ⊕ unit) m R)
  (v : matrix (m ⊕ unit) unit R)
  {hα: (vᵀ ⬝ v - vᵀ ⬝ X ⬝ (Xᵀ ⬝ X)⁻¹ ⬝ Xᵀ ⬝ v) 0 0 ≠ 0}
  [invertible (Xᵀ ⬝ X)] :
  let A : matrix m m R := (Xᵀ ⬝ X)⁻¹,
      α : R := (vᵀ ⬝ v - vᵀ ⬝ X ⬝ A ⬝ Xᵀ ⬝ v) 0 0,
      S11 : matrix m m R := α • A + A ⬝ Xᵀ ⬝ v ⬝ vᵀ ⬝ X ⬝ Aᵀ,
      S21 : matrix unit m R := -vᵀ ⬝ X ⬝ Aᵀ
  in (1 / α) • (Xᵀ ⬝ X ⬝ S11 + Xᵀ ⬝ v ⬝ S21) = 1 :=
begin
  have hA := is_unit_det_of_invertible (Xᵀ⬝X),
  intros A α S11 S21,
  simp_rw [matrix.mul_add, matrix.mul_smul, mul_inv_of_invertible, smul_add, ← smul_assoc, smul_eq_mul, 
    one_div_mul_cancel hα, one_smul], 
  change S21 with -vᵀ ⬝ X ⬝ Aᵀ, 
  simp_rw [matrix.neg_mul, matrix.mul_neg, smul_neg, tactic.ring.add_neg_eq_sub, 
    sub_eq_iff_eq_add, add_right_inj, matrix.mul_assoc A, 
    mul_nonsing_inv_cancel_left _ _ hA, ← matrix.mul_assoc],
end

lemma sS12 
  (X : matrix (m ⊕ unit) m R)
  (v : matrix (m ⊕ unit) unit R)
  [invertible (Xᵀ ⬝ X)] :
  let A : matrix m m R := (Xᵀ ⬝ X)⁻¹,
      α : R := (vᵀ ⬝ v - vᵀ ⬝ X ⬝ A ⬝ Xᵀ ⬝ v) 0 0,
      S12 : matrix m unit R := -A ⬝ Xᵀ ⬝ v,
      S22 : matrix unit unit R := 1
  in (1 / α) • (Xᵀ ⬝ X ⬝ S12 + Xᵀ ⬝ v ⬝ S22) = 0 :=
begin
  intros A α S12 S22,
  rw smul_eq_zero, 
  right,
  change S12 with -A ⬝ Xᵀ ⬝ v,
  rw [matrix.neg_mul, matrix.neg_mul, matrix.mul_neg, matrix.mul_assoc A,
    mul_nonsing_inv_cancel_left, matrix.mul_one, add_left_neg],
  apply is_unit_det_of_invertible,
end

lemma sS21
  (X : matrix (m ⊕ unit) m R)
  (v : matrix (m ⊕ unit) unit R)
  [invertible (Xᵀ ⬝ X)] :
  let A : matrix m m R := (Xᵀ ⬝ X)⁻¹,
      α : R := (vᵀ ⬝ v - vᵀ ⬝ X ⬝ A ⬝ Xᵀ ⬝ v) () (),
      S11 : matrix m m R := α • A + A ⬝ Xᵀ ⬝ v ⬝ vᵀ ⬝ X ⬝ Aᵀ,
      S21 : matrix unit m R := -vᵀ ⬝ X ⬝ Aᵀ
  in (1 / α) • (vᵀ ⬝ X ⬝ S11 + vᵀ ⬝ v ⬝ S21) = 0 :=
begin
  intros A α S11 S21,
  rw smul_eq_zero, 
  right,
  change S21 with -vᵀ ⬝ X ⬝ Aᵀ,
  simp_rw [matrix.mul_add, matrix.mul_smul, matrix.neg_mul, matrix.mul_neg],
  change α  with  (vᵀ ⬝ v - vᵀ ⬝ X ⬝ A ⬝ Xᵀ ⬝ v) () (),
  simp_rw [pi.sub_apply, sub_smul, fin_one_mul_eq_smul, ← sub_eq_add_neg,
    transpose_nonsing_inv, transpose_mul, transpose_transpose, ← matrix.mul_assoc,
    add_sub_assoc, sub_add_sub_cancel, sub_self],
end

lemma sS22
  (X : matrix (m ⊕ unit) m R)
  (v : matrix (m ⊕ unit) unit R)
  {hα: (vᵀ ⬝ v - vᵀ ⬝ X ⬝ (Xᵀ ⬝ X)⁻¹ ⬝ Xᵀ ⬝ v) 0 0 ≠ 0}
  [invertible (Xᵀ ⬝ X)]:
  let A : matrix m m R := (Xᵀ ⬝ X)⁻¹,
      α : R := (vᵀ ⬝ v - vᵀ ⬝ X ⬝ A ⬝ Xᵀ ⬝ v) 0 0,
      S12 : matrix m unit R := -A ⬝ Xᵀ ⬝ v,
      S22 : matrix unit unit R := 1
  in (1 / α) • (vᵀ ⬝ X ⬝ S12 + vᵀ ⬝ v ⬝ S22) = 1 :=
begin
  have f1 : ∀ (r: unit), r = 0, {intro r, simp only [eq_iff_true_of_subsingleton],},
  intros A α S12 S22,
  rw [one_div, inv_smul_eq_iff₀ hα, matrix.mul_one],
  change S12 with -A ⬝ Xᵀ ⬝ v,
  change α  with  (vᵀ ⬝ v - vᵀ ⬝ X ⬝ A ⬝ Xᵀ ⬝ v) 0 0,
  simp_rw [matrix.neg_mul, matrix.mul_neg],
  funext a b,
  simp_rw [f1 a, f1 b, pi.smul_apply, one_apply_eq, algebra.id.smul_eq_mul, mul_one, 
    neg_add_eq_sub, ← matrix.mul_assoc],
end

lemma eq_between_167_and_168 [invertible (Xᵀ⬝X)] 
  {hα: (vᵀ ⬝ v - vᵀ ⬝ X ⬝ (Xᵀ ⬝ X)⁻¹ ⬝ Xᵀ ⬝ v) 0 0 ≠ 0}: 
let 
  X' := (append_mat_vec X v), 
  A := (Xᵀ⬝X)⁻¹,
  α := ((vᵀ⬝v) - (vᵀ⬝X⬝A⬝Xᵀ⬝v)) 0 0,
  S11 := α•A + (A⬝Xᵀ⬝v⬝vᵀ⬝X⬝Aᵀ),    S12 := -A⬝Xᵀ⬝v,
  S21 := -vᵀ⬝X⬝Aᵀ,                  S22 := (1: matrix unit unit R),
  S :=  (1/α)•from_blocks S11 S12 S21 S22
in 
  (X'ᵀ⬝ X')⁻¹ = S := begin
  intros X' A α S11 S12 S21 S22 S,
  change X' with (append_mat_vec X v),
  
  rw rank_one_update_transpose_mul_self,
  apply inv_eq_right_inv,
  rw [matrix.mul_smul, from_blocks_multiply, from_blocks_smul, ← from_blocks_one],
  congr,
  apply sS11,
  exact hα,
  apply sS12,
  apply sS21,
  apply sS22,
  exact hα,
  -- { have f1 : ∀ (r: unit), r = 0, {intro r, simp only [eq_iff_true_of_subsingleton],},
  --   rw [one_div, inv_smul_eq_iff₀ hα, matrix.mul_one],
  --   change S12 with -A ⬝ Xᵀ ⬝ v,
  --   change α  with  (vᵀ ⬝ v - vᵀ ⬝ X ⬝ A ⬝ Xᵀ ⬝ v) 0 0,
  --   simp_rw [matrix.neg_mul, matrix.mul_neg],
  --   funext a b,
  --   simp_rw [f1 a, f1 b, pi.smul_apply, one_apply_eq, algebra.id.smul_eq_mul, mul_one, 
  --     neg_add_eq_sub, ← matrix.mul_assoc],
  -- }
end

end matrix_cookbook
