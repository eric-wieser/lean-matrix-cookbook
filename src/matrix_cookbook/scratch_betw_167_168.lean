import linear_algebra.matrix.nonsingular_inverse
import data.complex.basic
import matrix_cookbook.for_mathlib.linear_algebra.matrix.adjugate
import matrix_cookbook.for_mathlib.linear_algebra.matrix.nonsing_inverse
import linear_algebra.matrix.reindex

namespace matrix_cookbook

open matrix
open_locale matrix big_operators


variable z : ℕ
variable X : matrix (fin (z + 1)) (fin z) ℂ
variable v : matrix (fin (z + 1)) (fin 1) ℂ
def append_mat_vec := of (λ i, sum.elim (X i) (v i))
def e := @fin_sum_fin_equiv z 1
-- #check e z
-- #check @reindex_linear_equiv (fin z ⊕ fin 1) (fin z ⊕ fin 1) (fin (z + 1)) (fin (z + 1)) _ ℂ
#check reindex_linear_equiv_apply ℕ ℂ (e z) (e z)

-- lemma eq_between_167_and_168 : 
-- let 
--   X' := reindex (equiv.refl (fin (z+1))) (e z) (append_mat_vec z X v), 
--   A := (Xᵀ⬝X)⁻¹,
--   α := ((vᵀ⬝v) - (vᵀ⬝X⬝A⬝Xᵀ⬝v)) 0 0,
--   S11 := α•A + (A⬝Xᵀ⬝v⬝vᵀ⬝X⬝Aᵀ),    S12 := -A⬝Xᵀ⬝v,
--   S21 := -vᵀ⬝X⬝Aᵀ,                  S22 := 1,
--   S :=  (1/α)•from_blocks S11 S12 S21 S22
-- in 
--   (X'ᵀ⬝ X')⁻¹ = reindex (e z) (e z) S := begin
--   intros X' A α S11 S12 S21 S22 S,
--   apply inv_eq_left_inv,
--   rw ← matrix.mul_assoc,
--   change X' with reindex (equiv.refl (fin (z+1))) (e z) (append_mat_vec z X v),
--   rw matrix.transpose_reindex,
--   rw ← reindex_linear_equiv_apply ℕ ℂ (e z) (e z),
--   rw ← reindex_linear_equiv_apply ℕ ℂ (e z) (equiv.refl (fin (z+1))),
--   rw ← reindex_linear_equiv_apply ℕ ℂ (equiv.refl (fin (z+1))) (e z),
--   rw reindex_linear_equiv_mul ℕ ℂ (e z) (e z) (equiv.refl (fin (z+1))) S ((append_mat_vec z X v)ᵀ),
--   rw reindex_linear_equiv_mul ℕ ℂ (e z) (equiv.refl (fin (z+1))) (e z) (S⬝((append_mat_vec z X v)ᵀ)) ((append_mat_vec z X v)),
--   have : S ⬝ (append_mat_vec z X v)ᵀ ⬝ append_mat_vec z X v  = 1, {
--     extract_goal,
--   },
--   -- rw ← reindex_linear_equiv_apply ℕ ℂ (equiv.refl (fin (z+1))) (e z),
--   rw this,
--   exact matrix.reindex_linear_equiv_one,
-- end

example (z : ℕ)
  (X : matrix (fin (z + 1)) (fin z) ℂ)
  (v : matrix (fin (z + 1)) (fin 1) ℂ) :
let
  X' := reindex (equiv.refl (fin (z+1))) (e z) (append_mat_vec z X v), 
  A := (Xᵀ⬝X)⁻¹,
  α := ((vᵀ⬝v) - (vᵀ⬝X⬝A⬝Xᵀ⬝v)) 0 0,
  S11 := α•A + (A⬝Xᵀ⬝v⬝vᵀ⬝X⬝Aᵀ),    S12 := -A⬝Xᵀ⬝v,
  S21 := -vᵀ⬝X⬝Aᵀ,                  S22 := 1,
  S :=  (1/α)•from_blocks S11 S12 S21 S22
  in S ⬝ (append_mat_vec z X v)ᵀ ⬝ append_mat_vec z X v = 1 :=
begin
  intros X' A α S11 S12 S21 S22 S,
  
end



end matrix_cookbook