module

public import Mathlib.Analysis.Matrix.Normed

/-! # Comparisons between matrix norms

Copied from https://github.com/leanprover-community/mathlib4/pull/45196; delete once that lands in
the version of Mathlib we depend on.

* `Matrix.norm_le_linfty_opNorm`
* `Matrix.linfty_opNorm_le_card_nsmul_norm`
* `Matrix.norm_le_frobenius_norm`
* `Matrix.frobenius_norm_le_sqrt_card_mul_norm`
* `Matrix.linfty_opNorm_le_sqrt_card_mul_frobenius_norm`
* `Matrix.frobenius_norm_le_sqrt_card_mul_linfty_opNorm`
-/

@[expose] public section

open scoped NNReal

namespace Matrix

variable {R α : Type*} {m n : Type*} [Fintype m] [Fintype n]

/-! Prerequisites already in Mathlib `master` but newer than the version we depend on.

The rest of the file is from the PR. -/

section
variable [SeminormedAddCommGroup α]

open scoped Norms.Elementwise in
theorem nnnorm_apply_le_nnnorm (A : Matrix m n α) {i : m} {j : n} : ‖A i j‖₊ ≤ ‖A‖₊ :=
  nnnorm_entry_le_entrywise_sup_nnnorm A

open scoped Norms.Operator in
theorem nnnorm_apply_le_linfty_opNNNorm (A : Matrix m n α) (i : m) (j : n) : ‖A i j‖₊ ≤ ‖A‖₊ :=
  (PiLp.nnnorm_apply_le (WithLp.toLp 1 (A i)) j).trans
    (nnnorm_le_pi_nnnorm (fun i ↦ WithLp.toLp 1 (A i)) i)

end

/-- The elementwise norm never exceeds the $L_\infty$ operator norm. -/
lemma nnnorm_le_linfty_opNNNorm [SeminormedAddCommGroup R] (A : Matrix m n R) :
    (open scoped Norms.Elementwise in ‖A‖₊) ≤ (open scoped Norms.Operator in ‖A‖₊) :=
  nnnorm_le_iff.2 <| nnnorm_apply_le_linfty_opNNNorm A

/-- The elementwise norm never exceeds the $L_\infty$ operator norm. -/
lemma norm_le_linfty_opNorm [SeminormedAddCommGroup R] (A : Matrix m n R) :
    (open scoped Norms.Elementwise in ‖A‖) ≤ (open scoped Norms.Operator in ‖A‖) :=
  nnnorm_le_linfty_opNNNorm _

/-- The $L_\infty$ operator norm is bounded by a multiple of the elementwise norm. -/
lemma linfty_opNNNorm_le_card_nsmul_nnnorm [SeminormedAddCommGroup R] (A : Matrix m n R) :
    (open scoped Norms.Operator in ‖A‖₊) ≤
      Fintype.card n • (open scoped Norms.Elementwise in ‖A‖₊) := by
  rw [linfty_opNNNorm_def]
  exact Finset.sup_le fun i _ => Finset.sum_le_card_nsmul _ _ _ fun j _ => nnnorm_apply_le_nnnorm A

/-- The $L_\infty$ operator norm is bounded by a multiple of the elementwise norm. -/
lemma linfty_opNorm_le_card_nsmul_norm [SeminormedAddCommGroup R] (A : Matrix m n R) :
    (open scoped Norms.Operator in ‖A‖) ≤
      Fintype.card n • (open scoped Norms.Elementwise in ‖A‖) :=
  linfty_opNNNorm_le_card_nsmul_nnnorm _

section
open scoped Norms.Frobenius
variable [SeminormedAddCommGroup α]

theorem frobenius_nnnorm_le_iff {A : Matrix m n α} {r : ℝ≥0} :
    ‖A‖₊ ≤ r ↔ ∑ i, ∑ j, ‖A i j‖₊ ^ 2 ≤ r ^ 2 := by
  rw [frobenius_nnnorm_def, ← NNReal.sqrt_eq_rpow, NNReal.sqrt_le_iff_le_sq]
  simp

theorem le_frobenius_nnnorm_iff {A : Matrix m n α} {r : ℝ≥0} :
    r ≤ ‖A‖₊ ↔ r ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖₊ ^ 2 := by
  rw [frobenius_nnnorm_def, ← NNReal.sqrt_eq_rpow, NNReal.le_sqrt_iff_sq_le]
  simp

-- Already in Mathlib `master` but newer than the version we depend on.
theorem nnnorm_apply_le_frobenius_nnnorm (A : Matrix m n α) (i : m) (j : n) :
    ‖A i j‖₊ ≤ ‖A‖₊ := by
  grw [le_frobenius_nnnorm_iff, ← Finset.single_le_sum, ← Finset.single_le_sum] <;> simp

end

/-- The elementwise norm never exceeds the Frobenius norm. -/
lemma nnnorm_le_frobenius_nnnorm [SeminormedAddCommGroup R] (A : Matrix m n R) :
    (open scoped Norms.Elementwise in ‖A‖₊) ≤ (open scoped Norms.Frobenius in ‖A‖₊) :=
  nnnorm_le_iff.2 <| nnnorm_apply_le_frobenius_nnnorm A

/-- The elementwise norm never exceeds the Frobenius norm. -/
lemma norm_le_frobenius_norm [SeminormedAddCommGroup R] (A : Matrix m n R) :
    (open scoped Norms.Elementwise in ‖A‖) ≤ (open scoped Norms.Frobenius in ‖A‖) :=
  nnnorm_le_frobenius_nnnorm _

/-- The Frobenius norm is bounded by a multiple of the elementwise norm. -/
lemma frobenius_nnnorm_le_sqrt_card_mul_nnnorm [SeminormedAddCommGroup R] (A : Matrix m n R) :
    (open scoped Norms.Frobenius in ‖A‖₊) ≤
      .sqrt (Fintype.card m * Fintype.card n) * (open scoped Norms.Elementwise in ‖A‖₊) := by
  rw [frobenius_nnnorm_le_iff, mul_pow, NNReal.sq_sqrt]
  grw [nnnorm_apply_le_nnnorm A]
  simp [mul_assoc]

/-- The Frobenius norm is bounded by a multiple of the elementwise norm. -/
lemma frobenius_norm_le_sqrt_card_mul_norm [SeminormedAddCommGroup R] (A : Matrix m n R) :
    (open scoped Norms.Frobenius in ‖A‖) ≤
      √(Fintype.card m * Fintype.card n) * (open scoped Norms.Elementwise in ‖A‖) := by
  simpa using NNReal.coe_le_coe.mpr (frobenius_nnnorm_le_sqrt_card_mul_nnnorm A)

/-- The $L_\infty$ operator norm is bounded by a multiple of the Frobenius norm. -/
lemma linfty_opNNNorm_le_sqrt_card_mul_frobenius_nnnorm [SeminormedAddCommGroup R]
    (A : Matrix m n R) :
    (open scoped Norms.Operator in ‖A‖₊) ≤
      .sqrt (Fintype.card n) * (open scoped Norms.Frobenius in ‖A‖₊) := by
  rw [linfty_opNNNorm_def]
  refine Finset.sup_le fun i _ => ?_
  trans .sqrt (Fintype.card n) * ‖WithLp.toLp 2 (A i)‖₊
  · simpa [PiLp.nnnorm_eq_of_L2] using NNReal.sum_mul_le_sqrt_mul_sqrt Finset.univ 1 (‖A i ·‖₊)
  · gcongr
    exact PiLp.nnnorm_apply_le (WithLp.toLp 2 fun i ↦ WithLp.toLp 2 (A i)) i

/-- The $L_\infty$ operator norm is bounded by a multiple of the Frobenius norm. -/
lemma linfty_opNorm_le_sqrt_card_mul_frobenius_norm [SeminormedAddCommGroup R] (A : Matrix m n R) :
    (open scoped Norms.Operator in ‖A‖) ≤
      √(Fintype.card n) * (open scoped Norms.Frobenius in ‖A‖) := by
  simpa using NNReal.coe_le_coe.mpr (linfty_opNNNorm_le_sqrt_card_mul_frobenius_nnnorm A)

/-- The Frobenius norm is bounded by a multiple of the $L_\infty$ operator norm. -/
lemma frobenius_nnnorm_le_sqrt_card_mul_linfty_opNNNorm [SeminormedAddCommGroup R]
    (A : Matrix m n R) :
    (open scoped Norms.Frobenius in ‖A‖₊) ≤
      .sqrt (Fintype.card m) * (open scoped Norms.Operator in ‖A‖₊) := by
  rw [frobenius_nnnorm_le_iff, mul_pow, NNReal.sq_sqrt, linfty_opNNNorm_def, ← nsmul_eq_mul]
  refine Finset.sum_le_card_nsmul _ _ _ fun i hi => ?_
  grw [Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => zero_le, pow_le_pow_left₀ zero_le]
  exact Finset.le_sup (f := fun i => ∑ j, ‖A i j‖₊) hi

/-- The Frobenius norm is bounded by a multiple of the $L_\infty$ operator norm. -/
lemma frobenius_norm_le_sqrt_card_mul_linfty_opNorm [SeminormedAddCommGroup R] (A : Matrix m n R) :
    (open scoped Norms.Frobenius in ‖A‖) ≤
      √(Fintype.card m) * (open scoped Norms.Operator in ‖A‖) := by
  simpa using NNReal.coe_le_coe.mpr (frobenius_nnnorm_le_sqrt_card_mul_linfty_opNNNorm A)

end Matrix
