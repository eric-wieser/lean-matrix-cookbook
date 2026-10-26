module

public import Mathlib.Algebra.Regular.SMul
public import Mathlib.LinearAlgebra.Matrix.Symmetric

@[expose] public section

namespace Matrix

variable {n R : Type*} [Fintype n]

/-- If the quadratic form of a symmetric matrix vanishes, then its diagonal vanishes and twice the
matrix vanishes. See `Matrix.IsSymm.dotProduct_mulVec_self_eq_zero_iff` for the converse. -/
theorem IsSymm.diag_eq_zero_and_two_nsmul_eq_zero [NonAssocSemiring R] {A : Matrix n n R}
    (hA : A.IsSymm) (h : ∀ x, x ⬝ᵥ A *ᵥ x = 0) : A.diag = 0 ∧ 2 • A = 0 := by
  classical
  have hd : A.diag = 0 := funext fun i => by simpa using h (Pi.single i 1)
  refine ⟨hd, ?_⟩
  ext i j
  have hij := h (Pi.single i 1 + Pi.single j 1)
  simp only [mulVec_add, dotProduct_add, add_dotProduct, mulVec_single_one, single_one_dotProduct,
    col_apply, hA.apply i j] at hij
  rw [show A i i = 0 from congr_fun hd i, show A j j = 0 from congr_fun hd j, zero_add, add_zero,
    ← two_nsmul] at hij
  simpa using hij

/-- The quadratic form of a symmetric matrix vanishes iff its diagonal vanishes and twice the
matrix vanishes.

The reverse direction needs commutativity: over a noncommutative ring of characteristic 2, the
cross terms `x i * (A i j * x j) + x j * (A i j * x i)` need not cancel.

The left-hand side says that `Matrix.toLinearMap₂' R A` is alternating (`LinearMap.IsAlt`); compare
`LinearMap.isAlt_iff_eq_neg_flip`. See `LinearMap.IsSymmetric.inner_map_self_eq_zero` for the
inner-product-space version. -/
theorem IsSymm.dotProduct_mulVec_self_eq_zero_iff [CommSemiring R] {A : Matrix n n R}
    (hA : A.IsSymm) : (∀ x, x ⬝ᵥ A *ᵥ x = 0) ↔ A.diag = 0 ∧ 2 • A = 0 := by
  refine ⟨hA.diag_eq_zero_and_two_nsmul_eq_zero, fun ⟨hd, h2⟩ x => ?_⟩
  simp only [dotProduct, mulVec, Finset.mul_sum, ← Finset.sum_product']
  refine Finset.sum_involution (fun p _ => p.swap) (fun ⟨i, j⟩ _ => ?_) (fun ⟨i, j⟩ _ hne heq => ?_)
    (by simp) (by simp)
  · have : 2 * A i j = 0 := by simpa using congr_fun₂ h2 i j
    simp only [Prod.swap_prod_mk, hA.apply i j]
    calc _ = x i * x j * (A i j + A i j) := by rw [mul_add]; congr 1 <;> ac_rfl
      _ = 0 := by rw [← two_mul, this, mul_zero]
  · obtain rfl : j = i := congr_arg Prod.fst heq
    exact hne (by simp [show A j j = 0 from congr_fun hd j])

/-- A symmetric matrix is zero iff its quadratic form vanishes, provided `2` is cancellable.

See `LinearMap.IsSymmetric.inner_map_self_eq_zero` for the inner-product-space version. -/
theorem IsSymm.dotProduct_mulVec_self_eq_zero [NonAssocSemiring R] (h2 : IsSMulRegular R 2)
    {A : Matrix n n R} (hA : A.IsSymm) :
    (∀ x, x ⬝ᵥ A *ᵥ x = 0) ↔ A = 0 := by
  refine ⟨fun h => ?_, by rintro rfl; simp⟩
  ext i j
  exact h2 <| by simpa using congr_fun₂ (hA.diag_eq_zero_and_two_nsmul_eq_zero h).2 i j

end Matrix
