module

public import Mathlib.Algebra.Regular.SMul
public import Mathlib.LinearAlgebra.Matrix.Symmetric

@[expose] public section

namespace Matrix

variable {n R : Type*} [Fintype n]

/-- A symmetric matrix is zero iff its quadratic form vanishes, provided `2` is cancellable.

See `LinearMap.IsSymmetric.inner_map_self_eq_zero` for the inner-product-space version. -/
theorem IsSymm.dotProduct_mulVec_self_eq_zero [NonAssocSemiring R] (h2 : IsSMulRegular R 2)
    {A : Matrix n n R} (hA : A.IsSymm) :
    (∀ x, x ⬝ᵥ A *ᵥ x = 0) ↔ A = 0 := by
  classical
  refine ⟨fun h => ?_, by rintro rfl; simp⟩
  ext i j
  have hi := h (Pi.single i 1)
  have hj := h (Pi.single j 1)
  have hij := h (Pi.single i 1 + Pi.single j 1)
  simp only [mulVec_add, dotProduct_add, add_dotProduct, mulVec_single_one, single_one_dotProduct,
    col_apply, hA.apply i j] at hi hj hij
  rw [hi, hj, zero_add, add_zero, ← two_nsmul, ← smul_zero 2] at hij
  exact h2 hij

end Matrix
