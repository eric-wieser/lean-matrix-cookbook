module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Rank
public import MatrixCookbook.ForMathlib.Analysis.CStarAlgebra.Matrix

/-! # Rank-dependent bounds between matrix norms -/

@[expose] public section

open scoped NNReal ComplexOrder

namespace Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]

open scoped Norms.L2Operator in
/-- The eigenvalues of a Hermitian matrix are bounded by its $\ell^2$ operator norm. -/
lemma IsHermitian.abs_eigenvalues_le_l2_opNorm {A : Matrix n n 𝕜} (hA : A.IsHermitian) (i : n) :
    |hA.eigenvalues i| ≤ ‖A‖ := by
  simpa [hA.mulVec_eigenvectorBasis, norm_smul] using
    A.l2_opNorm_mulVec (hA.eigenvectorBasis i)

/-- The Frobenius norm is bounded by a multiple of the $\ell^2$ operator norm, depending on the
rank. -/
lemma frobenius_norm_le_sqrt_rank_mul_l2_opNorm (A : Matrix m n 𝕜) :
    (open scoped Norms.Frobenius in ‖A‖) ≤
      √A.rank * (open scoped Norms.L2Operator in ‖A‖) := by
  classical
  have hH := isHermitian_conjTranspose_mul_self A
  have key : ∑ i, ∑ j, ‖A i j‖ ^ 2 = ∑ k, hH.eigenvalues k := by
    have := congrArg RCLike.re hH.trace_eq_sum_eigenvalues
    simp [trace, mul_apply, RCLike.conj_mul] at this
    rwa [Finset.sum_comm] at this
  have hle : ∑ k, hH.eigenvalues k ≤ A.rank * (open scoped Norms.L2Operator in ‖A‖) ^ 2 := by
    open scoped Norms.L2Operator in
    rw [← Finset.sum_filter_ne_zero, ← rank_conjTranspose_mul_self, hH.rank_eq_card_non_zero_eigs,
      Fintype.card_subtype, ← nsmul_eq_mul, sq, ← l2_opNorm_conjTranspose_mul_self]
    exact Finset.sum_le_card_nsmul _ _ _ fun k _ =>
      (le_abs_self _).trans (hH.abs_eigenvalues_le_l2_opNorm k)
  have h0 : 0 ≤ (open scoped Norms.L2Operator in ‖A‖) :=
    open scoped Norms.L2Operator in norm_nonneg _
  open scoped Norms.Frobenius in
  rw [frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp_rw [Real.rpow_two, key]
  grw [hle, Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq h0]

end Matrix
