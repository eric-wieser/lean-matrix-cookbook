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

open scoped Norms.L2Operator in
/-- The trace of a Hermitian matrix is bounded by its rank times its $\ell^2$ operator norm. -/
lemma IsHermitian.re_trace_le_rank_mul_l2_opNorm {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    RCLike.re A.trace ≤ A.rank * ‖A‖ := by
  rw [hA.trace_eq_sum_eigenvalues, map_sum, hA.rank_eq_card_non_zero_eigs, Fintype.card_subtype,
    ← nsmul_eq_mul]
  simp_rw [RCLike.ofReal_re]
  rw [← Finset.sum_filter_ne_zero]
  exact Finset.sum_le_card_nsmul _ _ _ fun i _ =>
    (le_abs_self _).trans (hA.abs_eigenvalues_le_l2_opNorm i)

omit [DecidableEq n] in
open scoped Norms.Frobenius in
/-- The square of the Frobenius norm is the trace of `Aᴴ * A`. -/
lemma frobenius_norm_sq_eq_re_trace (A : Matrix m n 𝕜) : ‖A‖ ^ 2 = RCLike.re (Aᴴ * A).trace := by
  rw [frobenius_norm_def, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity), Finset.sum_comm]
  simp [trace, mul_apply, RCLike.conj_mul]

/-- The Frobenius norm is bounded by a multiple of the $\ell^2$ operator norm, depending on the
rank. -/
lemma frobenius_norm_le_sqrt_rank_mul_l2_opNorm (A : Matrix m n 𝕜) :
    (open scoped Norms.Frobenius in ‖A‖) ≤
      √A.rank * (open scoped Norms.L2Operator in ‖A‖) := by
  refine le_of_pow_le_pow_left₀ two_ne_zero
    (mul_nonneg (Real.sqrt_nonneg _) (open scoped Norms.L2Operator in norm_nonneg _)) ?_
  open scoped Norms.L2Operator in
  rw [frobenius_norm_sq_eq_re_trace, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), sq,
    ← l2_opNorm_conjTranspose_mul_self, ← rank_conjTranspose_mul_self]
  exact (isHermitian_conjTranspose_mul_self A).re_trace_le_rank_mul_l2_opNorm

end Matrix
