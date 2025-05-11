import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Matrix.Kronecker

namespace Matrix

variable {m n R}

/-- All the matrix entries, arranged into one column. -/
def vec (A : Matrix m n R) : n × m → R :=
  fun ij => A ij.2 ij.1

theorem vec_inj {A B : Matrix m n R} : A.vec = B.vec ↔ A = B := by
  simp_rw [← Matrix.ext_iff, funext_iff, Prod.forall, @forall_comm m n, vec]

theorem vec_zero [Zero R] : vec (0 : Matrix m n R) = 0 :=
  rfl

theorem vec_add [Add R] (A B : Matrix m n R) : vec (A + B) = vec A + vec B :=
  rfl

theorem vec_sub [Sub R] (A B : Matrix m n R) : vec (A - B) = vec A - vec B :=
  rfl

theorem vec_smul {α} [SMul α R] (r : α) (A : Matrix m n R) : vec (r • A) = r • vec A :=
  rfl

theorem vec_sum (s : Finset ι) [AddCommMonoid R] (A : ι → Matrix m n R) :
    vec (∑ i ∈ s, A i) = ∑ i ∈ s, vec (A i) := by
  ext
  simp_rw [vec, Finset.sum_apply, vec]
  erw [Finset.sum_apply, Finset.sum_apply]

variable [NonUnitalNonAssocRing R] [Fintype m] [Fintype n] in
theorem vec_dotProduct_vec (A B : Matrix m n R) : (vec A ⬝ᵥ vec B) = (Aᵀ * B).trace := by
  simp_rw [Matrix.trace, Matrix.diag, Matrix.mul_apply, dotProduct, vec, transpose_apply,
    ← Finset.univ_product_univ, Finset.sum_product]

section Kronecker
variable [NonUnitalCommRing R] [Fintype m] [Fintype n]
open scoped Kronecker

theorem kronecker_mulVec_vec (A : Matrix l m R) (X : Matrix m n R) (B : Matrix p n R) :
    B ⊗ₖ A *ᵥ vec X = vec (A * X * Bᵀ) := by
  ext ⟨k, l⟩
  simp_rw [vec, Matrix.mulVec, Matrix.mul_apply, dotProduct, Matrix.kroneckerMap_apply,
    Finset.sum_mul, transpose_apply, ← Finset.univ_product_univ, Finset.sum_product,
    mul_right_comm _ _ (B _ _), vec, mul_comm _ (B _ _)]

theorem vec_vecMul_kronecker (A : Matrix m l R) (X : Matrix m n R) (B : Matrix n p R) :
    vec X ᵥ* B ⊗ₖ A = vec (Aᵀ * X * B) := by
  rw [← mulVec_transpose, ← kroneckerMap_transpose, kronecker_mulVec_vec, transpose_transpose]

end Kronecker

end Matrix
