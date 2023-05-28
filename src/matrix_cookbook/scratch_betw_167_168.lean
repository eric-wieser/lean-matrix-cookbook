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

lemma eq_between_167_and_168 [invertible (Xᵀ⬝X)] [invertible ((vᵀ⬝v) - (vᵀ⬝X⬝(Xᵀ⬝X)⁻¹⬝Xᵀ⬝v))]: 
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
  have : (append_mat_vec z X v)ᵀ ⬝ append_mat_vec z X v  = 
    from_blocks (Xᵀ⬝X) (Xᵀ⬝v) (vᵀ⬝X) (vᵀ⬝v), {
    -- extract_goal,
    sorry,
  },
  rw this,
  apply inv_eq_right_inv,
  rw matrix.mul_smul,
  rw from_blocks_multiply,
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