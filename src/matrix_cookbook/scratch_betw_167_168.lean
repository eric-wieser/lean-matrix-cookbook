import linear_algebra.matrix.nonsingular_inverse
import data.complex.basic
import matrix_cookbook.for_mathlib.linear_algebra.matrix.adjugate
import matrix_cookbook.for_mathlib.linear_algebra.matrix.nonsing_inverse
import linear_algebra.matrix.reindex

namespace matrix_cookbook

open matrix
open_locale matrix big_operators

variables {m n R: Type*}[fintype m][fintype n][decidable_eq m][decidable_eq n]
variables [field R]

lemma reindex_equiv_eq_if_matrix_eq (e₁ e₂ : n ≃ m) (A B: matrix n n R) : 
  (reindex e₁ e₂ A = reindex e₁ e₂ B) → A = B :=
begin
  intro h,
  rw ← matrix.ext_iff at h,
  funext r s,
  specialize h (e₁ r) (e₂ s),
  simp only [reindex_apply, submatrix_apply, equiv.symm_apply_apply] at h,
  exact h,
end

lemma matrix_eq_if_reindex_equiv (e₁ e₂ : n ≃ m) (A B: matrix n n R) : 
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
variable X : matrix (fin (z + 1)) (fin z) ℂ
variable v : matrix (fin (z + 1)) (fin 1) ℂ
def append_mat_vec := of (λ i, sum.elim (X i) (v i))
def e := @fin_sum_fin_equiv z 1
-- #check e z
-- #check @reindex_linear_equiv (fin z ⊕ fin 1) (fin z ⊕ fin 1) (fin (z + 1)) (fin (z + 1)) _ ℂ
-- #check reindex_linear_equiv_apply ℕ ℂ (e z) (e z)

lemma rank_one_update_transpose_mul_self (z : ℕ)
  (X : matrix (fin (z + 1)) (fin z) ℂ)
  (v : matrix (fin (z + 1)) (fin 1) ℂ)
  [invertible (Xᵀ ⬝ X)] :
  (append_mat_vec z X v)ᵀ ⬝ append_mat_vec z X v =
    from_blocks (Xᵀ ⬝ X) (Xᵀ ⬝ v) (vᵀ ⬝ X) (vᵀ ⬝ v) :=
begin
  admit,
end


lemma sS11 {z : ℕ} {X : matrix (fin (z + 1)) (fin z) ℂ} {v : matrix (fin (z + 1)) (fin 1) ℂ}
  {hα: (vᵀ ⬝ v - vᵀ ⬝ X ⬝ (Xᵀ ⬝ X)⁻¹ ⬝ Xᵀ ⬝ v) 0 0 ≠ 0}
  [invertible (Xᵀ ⬝ X)] :
  let A : matrix (fin z) (fin z) ℂ := (Xᵀ ⬝ X)⁻¹,
      α : ℂ := (vᵀ ⬝ v - vᵀ ⬝ X ⬝ A ⬝ Xᵀ ⬝ v) 0 0,
      S11 : matrix (fin z) (fin z) ℂ := α • A + A ⬝ Xᵀ ⬝ v ⬝ vᵀ ⬝ X ⬝ Aᵀ,
      S21 : matrix (fin 1) (fin z) ℂ := -vᵀ ⬝ X ⬝ Aᵀ
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
  (X : matrix (fin (z + 1)) (fin z) ℂ)
  (v : matrix (fin (z + 1)) (fin 1) ℂ)
  [invertible (Xᵀ ⬝ X)] :
  let A : matrix (fin z) (fin z) ℂ := (Xᵀ ⬝ X)⁻¹,
      α : ℂ := (vᵀ ⬝ v - vᵀ ⬝ X ⬝ A ⬝ Xᵀ ⬝ v) 0 0,
      S12 : matrix (fin z) (fin 1) ℂ := -A ⬝ Xᵀ ⬝ v,
      S22 : matrix (fin 1) (fin 1) ℂ := 1
  in (1 / α) • (Xᵀ ⬝ X ⬝ S12 + Xᵀ ⬝ v ⬝ S22) = 0 :=
begin
  intros A α S12 S22,
  rw [smul_eq_zero], 
  right,
  change S12 with -A ⬝ Xᵀ ⬝ v,
  rw [matrix.neg_mul, matrix.neg_mul, matrix.mul_neg, matrix.mul_assoc A,
    mul_nonsing_inv_cancel_left, matrix.mul_one, add_left_neg],
  apply is_unit_det_of_invertible,
end

lemma sS21 (z : ℕ)
  (X : matrix (fin (z + 1)) (fin z) ℂ)
  (v : matrix (fin (z + 1)) (fin 1) ℂ)
  [invertible (Xᵀ ⬝ X)] :
  let A : matrix (fin z) (fin z) ℂ := (Xᵀ ⬝ X)⁻¹,
      α : ℂ := (vᵀ ⬝ v - vᵀ ⬝ X ⬝ A ⬝ Xᵀ ⬝ v) 0 0,
      S11 : matrix (fin z) (fin z) ℂ := α • A + A ⬝ Xᵀ ⬝ v ⬝ vᵀ ⬝ X ⬝ Aᵀ,
      S21 : matrix (fin 1) (fin z) ℂ := -vᵀ ⬝ X ⬝ Aᵀ
  in (1 / α) • (vᵀ ⬝ X ⬝ S11 + vᵀ ⬝ v ⬝ S21) = 0 :=
begin
  intros A α S11 S21,
  rw smul_eq_zero, right,
  change S11 with α • A + A ⬝ Xᵀ ⬝ v ⬝ vᵀ ⬝ X ⬝ Aᵀ,
  change S21 with -vᵀ ⬝ X ⬝ Aᵀ,
  change A with (Xᵀ ⬝ X)⁻¹,
  
  rw matrix.mul_add, rw matrix.mul_smul,
  simp only [matrix.neg_mul, matrix.mul_neg],
  change α  with  (vᵀ ⬝ v - vᵀ ⬝ X ⬝ A ⬝ Xᵀ ⬝ v) 0 0,
  rw pi.sub_apply, 
  rw pi.sub_apply, 
  rw sub_smul,
  change A with (Xᵀ ⬝ X)⁻¹,
  
end

lemma sS22 (z : ℕ)
  (X : matrix (fin (z + 1)) (fin z) ℂ)
  (v : matrix (fin (z + 1)) (fin 1) ℂ)
  [invertible (Xᵀ ⬝ X)]:
  let A : matrix (fin z) (fin z) ℂ := (Xᵀ ⬝ X)⁻¹,
      α : ℂ := (vᵀ ⬝ v - vᵀ ⬝ X ⬝ A ⬝ Xᵀ ⬝ v) 0 0,
      S12 : matrix (fin z) (fin 1) ℂ := -A ⬝ Xᵀ ⬝ v,
      S22 : matrix (fin 1) (fin 1) ℂ := 1
  in (1 / α) • (vᵀ ⬝ X ⬝ S12 + vᵀ ⬝ v ⬝ S22) = 1 :=
begin
  intros A α S12 S22,
  admit,
end

lemma eq_between_167_and_168 [invertible (Xᵀ⬝X)] 
  {hα: (vᵀ ⬝ v - vᵀ ⬝ X ⬝ (Xᵀ ⬝ X)⁻¹ ⬝ Xᵀ ⬝ v) 0 0 ≠ 0}: 
let 
  X' := reindex (equiv.refl (fin (z+1))) (e z) (append_mat_vec z X v), 
  A := (Xᵀ⬝X)⁻¹,
  α := ((vᵀ⬝v) - (vᵀ⬝X⬝A⬝Xᵀ⬝v)) 0 0,
  S11 := α•A + (A⬝Xᵀ⬝v⬝vᵀ⬝X⬝Aᵀ),    S12 := -A⬝Xᵀ⬝v,
  S21 := -vᵀ⬝X⬝Aᵀ,                  S22 := (1: matrix (fin 1) (fin 1) ℂ),
  S :=  (1/α)•from_blocks S11 S12 S21 S22
in 
  (X'ᵀ⬝ X')⁻¹ = reindex (e z) (e z) S := begin
  intros X' A α S11 S12 S21 S22 S,
  change X' with reindex (equiv.refl (fin (z+1))) (e z) (append_mat_vec z X v),
  rw matrix.transpose_reindex,
  rw ← reindex_linear_equiv_apply ℕ ℂ (e z) (e z),
  rw ← reindex_linear_equiv_apply ℕ ℂ (e z) (equiv.refl (fin (z+1))),
  rw ← reindex_linear_equiv_apply ℕ ℂ (equiv.refl (fin (z+1))) (e z),
  rw reindex_linear_equiv_mul ℕ ℂ (e z) (equiv.refl (fin (z+1))) (e z) 
    (append_mat_vec z X v)ᵀ ((append_mat_vec z X v)),
  rw reindex_linear_equiv_apply ℕ ℂ (e z) (e z),
  rw reindex_linear_equiv_apply ℕ ℂ (e z) (e z),
  rw matrix.inv_reindex (e z) (e z),
  rw reindex_equiv_eq_iff_matrix_eq,
  rw rank_one_update_transpose_mul_self,
  apply inv_eq_right_inv,
  rw matrix.mul_smul,
  rw from_blocks_multiply,
  rw from_blocks_smul,
  rw ← from_blocks_one,
  congr,
  apply sS11, assumption',
  apply sS12,
  apply sS21,
  apply sS22,
end



-- example (z : ℕ)
--   (X : matrix (fin (z + 1)) (fin z) ℂ)
--   (v : matrix (fin (z + 1)) (fin 1) ℂ) :
--   let X' : matrix (fin (z + 1)) (fin (z + 1)) ℂ :=
--         ⇑(reindex (equiv.refl (fin (z + 1))) (e z)) (append_mat_vec z X v),
--       A : matrix (fin z) (fin z) ℂ := (Xᵀ ⬝ X)⁻¹,
--       α : ℂ := (vᵀ ⬝ v - vᵀ ⬝ X ⬝ A ⬝ Xᵀ ⬝ v) 0 0,
--       S11 : matrix (fin z) (fin z) ℂ :=
--         α • A + A ⬝ Xᵀ ⬝ v ⬝ vᵀ ⬝ X ⬝ Aᵀ,
--       S12 : matrix (fin z) (fin 1) ℂ := -A ⬝ Xᵀ ⬝ v,
--       S21 : matrix (fin 1) (fin z) ℂ := -vᵀ ⬝ X ⬝ Aᵀ,
--       S22 : ℕ := 1,
--       S : matrix (fin z ⊕ fin 1) (fin z ⊕ fin 1) ℂ :=
--         (1 / α) • from_blocks S11 S12 S21 ↑S22
--   in (append_mat_vec z X v)ᵀ ⬝ append_mat_vec z X v =
--        from_blocks (Xᵀ ⬝ X) (Xᵀ ⬝ v) (vᵀ ⬝ X) (vᵀ ⬝ v) :=
-- begin
--   intros X' A α S11 S12 S21 S22 S,
--   admit,
-- end





end matrix_cookbook