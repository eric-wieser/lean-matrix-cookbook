module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import MatrixCookbook.ForMathlib.Analysis.Matrix.Normed

/-! # Comparisons between the $\ell^2$ operator norm and other matrix norms

Copied from https://github.com/leanprover-community/mathlib4/pull/45196; delete once that lands in
the version of Mathlib we depend on.

* `Matrix.norm_le_l2_opNorm`, `Matrix.l2_opNorm_le_sqrt_card_mul_norm`: comparison with the
  elementwise norm.
* `Matrix.l2_opNorm_le_frobenius_norm`, `Matrix.frobenius_norm_le_sqrt_min_card_mul_l2_opNorm`:
  comparison with the Frobenius norm.
* `Matrix.l2_opNorm_le_sqrt_card_mul_linfty_opNorm`,
  `Matrix.linfty_opNorm_le_sqrt_card_mul_l2_opNorm`: comparison with the $L^\infty$ operator norm.
-/

@[expose] public section

open scoped NNReal
open WithLp (toLp)

namespace Matrix

variable {𝕜 m n : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [DecidableEq n]

section
open scoped Norms.L2Operator

lemma nnnorm_apply_le_l2_opNNNorm (A : Matrix m n 𝕜) (i : m) (j : n) : ‖A i j‖₊ ≤ ‖A‖₊ := by
  simpa using (PiLp.nnnorm_apply_le (toLp 2 (A *ᵥ Pi.single j 1)) i).trans
    (A.l2_opNNNorm_mulVec (PiLp.single 2 j 1))

lemma norm_apply_le_l2_opNorm (A : Matrix m n 𝕜) (i : m) (j : n) : ‖A i j‖ ≤ ‖A‖ :=
  nnnorm_apply_le_l2_opNNNorm A i j

end

/-- The elementwise norm never exceeds the $\ell^2$ operator norm. -/
lemma nnnorm_le_l2_opNNNorm (A : Matrix m n 𝕜) :
    (open scoped Norms.Elementwise in ‖A‖₊) ≤ (open scoped Norms.L2Operator in ‖A‖₊) :=
  nnnorm_le_iff.2 <| nnnorm_apply_le_l2_opNNNorm A

/-- The elementwise norm never exceeds the $\ell^2$ operator norm. -/
lemma norm_le_l2_opNorm (A : Matrix m n 𝕜) :
    (open scoped Norms.Elementwise in ‖A‖) ≤ (open scoped Norms.L2Operator in ‖A‖) :=
  nnnorm_le_l2_opNNNorm A

/-- The $\ell^2$ operator norm never exceeds the Frobenius norm. -/
lemma l2_opNNNorm_le_frobenius_nnnorm (A : Matrix m n 𝕜) :
    (open scoped Norms.L2Operator in ‖A‖₊) ≤ (open scoped Norms.Frobenius in ‖A‖₊) := by
  refine ContinuousLinearMap.opNNNorm_le_bound _ _ fun x => ?_
  change ‖toLp 2 (A *ᵥ x)‖₊ ≤ _ * ‖x‖₊
  rw [← frobenius_nnnorm_replicateCol (ι := Fin 1), ← x.toLp_ofLp,
    ← frobenius_nnnorm_replicateCol (ι := Fin 1)]
  exact frobenius_nnnorm_mul A (replicateCol (Fin 1) x)

/-- The $\ell^2$ operator norm never exceeds the Frobenius norm. -/
lemma l2_opNorm_le_frobenius_norm (A : Matrix m n 𝕜) :
    (open scoped Norms.L2Operator in ‖A‖) ≤ (open scoped Norms.Frobenius in ‖A‖) :=
  l2_opNNNorm_le_frobenius_nnnorm A

/-- The $\ell^2$ operator norm is bounded by a multiple of the elementwise norm. -/
lemma l2_opNNNorm_le_sqrt_card_mul_nnnorm (A : Matrix m n 𝕜) :
    (open scoped Norms.L2Operator in ‖A‖₊) ≤
      .sqrt (Fintype.card m * Fintype.card n) * (open scoped Norms.Elementwise in ‖A‖₊) :=
  (l2_opNNNorm_le_frobenius_nnnorm A).trans (frobenius_nnnorm_le_sqrt_card_mul_nnnorm A)

/-- The $\ell^2$ operator norm is bounded by a multiple of the elementwise norm. -/
lemma l2_opNorm_le_sqrt_card_mul_norm (A : Matrix m n 𝕜) :
    (open scoped Norms.L2Operator in ‖A‖) ≤
      √(Fintype.card m * Fintype.card n) * (open scoped Norms.Elementwise in ‖A‖) := by
  simpa using NNReal.coe_le_coe.mpr (l2_opNNNorm_le_sqrt_card_mul_nnnorm A)

/-- The Frobenius norm is bounded by a multiple of the $\ell^2$ operator norm. -/
lemma frobenius_nnnorm_le_sqrt_card_right_mul_l2_opNNNorm (A : Matrix m n 𝕜) :
    (open scoped Norms.Frobenius in ‖A‖₊) ≤
      .sqrt (Fintype.card n) * (open scoped Norms.L2Operator in ‖A‖₊) := by
  rw [frobenius_nnnorm_le_iff, mul_pow, NNReal.sq_sqrt, @Finset.sum_comm _ _ m, ← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun j _ => ?_
  simpa [PiLp.nnnorm_eq_of_L2, NNReal.sqrt_le_iff_le_sq] using
    A.l2_opNNNorm_mulVec (PiLp.single 2 j 1)

/-- The Frobenius norm is bounded by a multiple of the $\ell^2$ operator norm. -/
lemma frobenius_norm_le_sqrt_card_right_mul_l2_opNorm (A : Matrix m n 𝕜) :
    (open scoped Norms.Frobenius in ‖A‖) ≤
      √(Fintype.card n) * (open scoped Norms.L2Operator in ‖A‖) := by
  simpa using NNReal.coe_le_coe.mpr (frobenius_nnnorm_le_sqrt_card_right_mul_l2_opNNNorm A)

/-- The Frobenius norm is bounded by a multiple of the $\ell^2$ operator norm. -/
lemma frobenius_nnnorm_le_sqrt_card_left_mul_l2_opNNNorm (A : Matrix m n 𝕜) :
    (open scoped Norms.Frobenius in ‖A‖₊) ≤
      .sqrt (Fintype.card m) * (open scoped Norms.L2Operator in ‖A‖₊) := by
  classical
  simpa [l2_opNNNorm_conjTranspose] using frobenius_nnnorm_le_sqrt_card_right_mul_l2_opNNNorm Aᴴ

/-- The Frobenius norm is bounded by a multiple of the $\ell^2$ operator norm. -/
lemma frobenius_norm_le_sqrt_card_left_mul_l2_opNorm (A : Matrix m n 𝕜) :
    (open scoped Norms.Frobenius in ‖A‖) ≤
      √(Fintype.card m) * (open scoped Norms.L2Operator in ‖A‖) := by
  simpa using NNReal.coe_le_coe.mpr (frobenius_nnnorm_le_sqrt_card_left_mul_l2_opNNNorm A)

/-- The Frobenius norm is bounded by a multiple of the $\ell^2$ operator norm. -/
lemma frobenius_nnnorm_le_sqrt_min_card_mul_l2_opNNNorm (A : Matrix m n 𝕜) :
    (open scoped Norms.Frobenius in ‖A‖₊) ≤
      .sqrt (min (Fintype.card m) (Fintype.card n)) * (open scoped Norms.L2Operator in ‖A‖₊) := by
  rcases le_total (Fintype.card m) (Fintype.card n) with h | h
  · simpa [h] using frobenius_nnnorm_le_sqrt_card_left_mul_l2_opNNNorm A
  · simpa [h] using frobenius_nnnorm_le_sqrt_card_right_mul_l2_opNNNorm A

/-- The Frobenius norm is bounded by a multiple of the $\ell^2$ operator norm. -/
lemma frobenius_norm_le_sqrt_min_card_mul_l2_opNorm (A : Matrix m n 𝕜) :
    (open scoped Norms.Frobenius in ‖A‖) ≤
      √(min (Fintype.card m) (Fintype.card n)) * (open scoped Norms.L2Operator in ‖A‖) := by
  simpa [← Real.sqrt_monotone.map_min] using
    NNReal.coe_le_coe.mpr (frobenius_nnnorm_le_sqrt_min_card_mul_l2_opNNNorm A)

/-- The $\ell^2$ operator norm is bounded by a multiple of the $L_\infty$ operator norm. -/
lemma l2_opNNNorm_le_sqrt_card_mul_linfty_opNNNorm (A : Matrix m n 𝕜) :
    (open scoped Norms.L2Operator in ‖A‖₊) ≤
      .sqrt (Fintype.card m) * (open scoped Norms.Operator in ‖A‖₊) :=
  (l2_opNNNorm_le_frobenius_nnnorm A).trans (frobenius_nnnorm_le_sqrt_card_mul_linfty_opNNNorm A)

/-- The $\ell^2$ operator norm is bounded by a multiple of the $L_\infty$ operator norm. -/
lemma l2_opNorm_le_sqrt_card_mul_linfty_opNorm (A : Matrix m n 𝕜) :
    (open scoped Norms.L2Operator in ‖A‖) ≤
      √(Fintype.card m) * (open scoped Norms.Operator in ‖A‖) := by
  simpa using NNReal.coe_le_coe.mpr (l2_opNNNorm_le_sqrt_card_mul_linfty_opNNNorm A)

/-- The $L_\infty$ operator norm is bounded by a multiple of the $\ell^2$ operator norm. -/
lemma linfty_opNNNorm_le_sqrt_card_mul_l2_opNNNorm (A : Matrix m n 𝕜) :
    (open scoped Norms.Operator in ‖A‖₊) ≤
      .sqrt (Fintype.card n) * (open scoped Norms.L2Operator in ‖A‖₊) := by
  classical
  rw [linfty_opNNNorm_def]
  refine Finset.sup_le fun i _ => ?_
  trans .sqrt (Fintype.card n) * ‖toLp 2 (Aᴴ *ᵥ Pi.single i 1)‖₊
  · simpa [PiLp.nnnorm_eq_of_L2] using NNReal.sum_mul_le_sqrt_mul_sqrt Finset.univ 1 (‖A i ·‖₊)
  · gcongr
    simpa [l2_opNNNorm_conjTranspose] using Aᴴ.l2_opNNNorm_mulVec (PiLp.single 2 i 1)

/-- The $L_\infty$ operator norm is bounded by a multiple of the $\ell^2$ operator norm. -/
lemma linfty_opNorm_le_sqrt_card_mul_l2_opNorm (A : Matrix m n 𝕜) :
    (open scoped Norms.Operator in ‖A‖) ≤
      √(Fintype.card n) * (open scoped Norms.L2Operator in ‖A‖) := by
  simpa using NNReal.coe_le_coe.mpr (linfty_opNNNorm_le_sqrt_card_mul_l2_opNNNorm A)

end Matrix
