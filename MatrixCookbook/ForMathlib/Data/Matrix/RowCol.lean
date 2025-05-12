import Mathlib.Data.Matrix.RowCol

namespace Matrix

variable {l m n α : Type*}
variable [DecidableEq m] [Fintype m] [NonUnitalNonAssocSemiring α]

@[simp]
theorem updateCol_zero_mul_updateRow_zero_of_eq
    (i : m) (r : l → α) (c : n → α):
    (0 : Matrix l m α).updateCol i r * (0 : Matrix m n α).updateRow i c = vecMulVec r c := by
  ext i' j'
  simp [mul_apply, vecMulVec, updateRow_apply]

@[simp]
theorem updateCol_zero_mul_updateRow_zero_of_ne
    (i : m) (r : l → α) (j : m) (c : n → α) (hij : i ≠ j):
    (0 : Matrix l m α).updateCol i r * (0 : Matrix m n α).updateRow j c = 0 := by
  ext i' j'
  simp [mul_apply, vecMulVec, updateRow_apply, hij, hij.symm]

end Matrix
