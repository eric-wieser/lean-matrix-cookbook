import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.reindex

namespace matrix_cookbook

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

variable z : ℕ
variable X : matrix (fin (z + 1)) (fin z) R
variable v : matrix (fin (z + 1)) (fin 1) R
def append_mat_vec := of (λ i, sum.elim (X i) (v i))
def e := @fin_sum_fin_equiv z 1

lemma rank_one_update_transpose_mul_self (z : ℕ)
  (X : matrix (fin (z + 1)) (fin z) R)
  (v : matrix (fin (z + 1)) (fin 1) R)
  [invertible (Xᵀ ⬝ X)] :
  (append_mat_vec z X v)ᵀ ⬝ append_mat_vec z X v =
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

lemma fin_one_mul_eq_smul {A: matrix (fin 1) m R} {q: matrix (fin 1) (fin 1) R}:
  (q 0 0) • A = q ⬝ A := 
begin
  funext r s,
  have : r = 0, {simp only [eq_iff_true_of_subsingleton],},
  rw [mul_apply, pi.smul_apply, pi.smul_apply, algebra.id.smul_eq_mul,fintype.univ_of_subsingleton,
    fin.mk_zero, finset.sum_singleton, this],
end

lemma sS11 {z : ℕ} {X : matrix (fin (z + 1)) (fin z) R} {v : matrix (fin (z + 1)) (fin 1) R}
  {hα: (vᵀ ⬝ v - vᵀ ⬝ X ⬝ (Xᵀ ⬝ X)⁻¹ ⬝ Xᵀ ⬝ v) 0 0 ≠ 0}
  [invertible (Xᵀ ⬝ X)] :
  let A : matrix (fin z) (fin z) R := (Xᵀ ⬝ X)⁻¹,
      α : R := (vᵀ ⬝ v - vᵀ ⬝ X ⬝ A ⬝ Xᵀ ⬝ v) 0 0,
      S11 : matrix (fin z) (fin z) R := α • A + A ⬝ Xᵀ ⬝ v ⬝ vᵀ ⬝ X ⬝ Aᵀ,
      S21 : matrix (fin 1) (fin z) R := -vᵀ ⬝ X ⬝ Aᵀ
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

lemma sS12 (z : ℕ)
  (X : matrix (fin (z + 1)) (fin z) R)
  (v : matrix (fin (z + 1)) (fin 1) R)
  [invertible (Xᵀ ⬝ X)] :
  let A : matrix (fin z) (fin z) R := (Xᵀ ⬝ X)⁻¹,
      α : R := (vᵀ ⬝ v - vᵀ ⬝ X ⬝ A ⬝ Xᵀ ⬝ v) 0 0,
      S12 : matrix (fin z) (fin 1) R := -A ⬝ Xᵀ ⬝ v,
      S22 : matrix (fin 1) (fin 1) R := 1
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

lemma sS21 (z : ℕ)
  (X : matrix (fin (z + 1)) (fin z) R)
  (v : matrix (fin (z + 1)) (fin 1) R)
  [invertible (Xᵀ ⬝ X)] :
  let A : matrix (fin z) (fin z) R := (Xᵀ ⬝ X)⁻¹,
      α : R := (vᵀ ⬝ v - vᵀ ⬝ X ⬝ A ⬝ Xᵀ ⬝ v) 0 0,
      S11 : matrix (fin z) (fin z) R := α • A + A ⬝ Xᵀ ⬝ v ⬝ vᵀ ⬝ X ⬝ Aᵀ,
      S21 : matrix (fin 1) (fin z) R := -vᵀ ⬝ X ⬝ Aᵀ
  in (1 / α) • (vᵀ ⬝ X ⬝ S11 + vᵀ ⬝ v ⬝ S21) = 0 :=
begin
  intros A α S11 S21,
  rw smul_eq_zero, 
  right,
  change S21 with -vᵀ ⬝ X ⬝ Aᵀ,
  simp_rw [matrix.mul_add, matrix.mul_smul, matrix.neg_mul, matrix.mul_neg],
  change α  with  (vᵀ ⬝ v - vᵀ ⬝ X ⬝ A ⬝ Xᵀ ⬝ v) 0 0,
  simp_rw [pi.sub_apply, sub_smul, fin_one_mul_eq_smul, ← sub_eq_add_neg,
    transpose_nonsing_inv, transpose_mul, transpose_transpose, ← matrix.mul_assoc,
    add_sub_assoc, sub_add_sub_cancel, sub_self],
end

lemma sS22 (z : ℕ)
  (X : matrix (fin (z + 1)) (fin z) R)
  (v : matrix (fin (z + 1)) (fin 1) R)
  {hα: (vᵀ ⬝ v - vᵀ ⬝ X ⬝ (Xᵀ ⬝ X)⁻¹ ⬝ Xᵀ ⬝ v) 0 0 ≠ 0}
  [invertible (Xᵀ ⬝ X)]:
  let A : matrix (fin z) (fin z) R := (Xᵀ ⬝ X)⁻¹,
      α : R := (vᵀ ⬝ v - vᵀ ⬝ X ⬝ A ⬝ Xᵀ ⬝ v) 0 0,
      S12 : matrix (fin z) (fin 1) R := -A ⬝ Xᵀ ⬝ v,
      S22 : matrix (fin 1) (fin 1) R := 1
  in (1 / α) • (vᵀ ⬝ X ⬝ S12 + vᵀ ⬝ v ⬝ S22) = 1 :=
begin
  have f1 : ∀ (r: fin 1), r = 0, {intro r, simp only [eq_iff_true_of_subsingleton],},
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
  X' := reindex (equiv.refl (fin (z+1))) (e z) (append_mat_vec z X v), 
  A := (Xᵀ⬝X)⁻¹,
  α := ((vᵀ⬝v) - (vᵀ⬝X⬝A⬝Xᵀ⬝v)) 0 0,
  S11 := α•A + (A⬝Xᵀ⬝v⬝vᵀ⬝X⬝Aᵀ),    S12 := -A⬝Xᵀ⬝v,
  S21 := -vᵀ⬝X⬝Aᵀ,                  S22 := (1: matrix (fin 1) (fin 1) R),
  S :=  (1/α)•from_blocks S11 S12 S21 S22
in 
  (X'ᵀ⬝ X')⁻¹ = reindex (e z) (e z) S := begin
  intros X' A α S11 S12 S21 S22 S,
  change X' with reindex (equiv.refl (fin (z+1))) (e z) (append_mat_vec z X v),
  
  let Zre := reindex_linear_equiv_apply ℕ R (e z) (e z),
  let Zr1 := reindex_linear_equiv_apply ℕ R (e z) (equiv.refl (fin (z+1))),
  let Zr2 := reindex_linear_equiv_apply ℕ R (equiv.refl (fin (z+1))) (e z),
  let Zr3 := reindex_linear_equiv_mul ℕ R (e z) (equiv.refl (fin (z+1))) (e z),
  
  rw [matrix.transpose_reindex, ← Zre, ← Zr1, ← Zr2, 
    Zr3 (append_mat_vec z X v)ᵀ ((append_mat_vec z X v)), 
    Zre, Zre], 

  simp_rw [matrix.inv_reindex (e z) (e z), reindex_equiv_eq_iff_matrix_eq,
    rank_one_update_transpose_mul_self],
  apply inv_eq_right_inv,
  rw [matrix.mul_smul, from_blocks_multiply, from_blocks_smul, ← from_blocks_one],
  congr,
  apply sS11, assumption',
  apply sS12,
  apply sS21,
  apply sS22, assumption',
end

end matrix_cookbook
