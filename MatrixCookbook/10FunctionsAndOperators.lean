import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Data.Real.NNReal
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.NormedSpace.MatrixExponential
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Functions and Operators -/

variable {ι : Type _} {R : Type _} {l m n p q r : Type _}

variable [Fintype l] [Fintype m] [Fintype n] [Fintype p] [Fintype q] [Fintype r]

variable [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
  [DecidableEq r]

open scoped Nat BigOperators Matrix NNReal ENNReal

open Matrix

namespace MatrixCookbook

variable [Field R]

/-! ### Functions and Series -/


/-! #### Finite Series -/


/-- The pdf does not mention `hx`! -/
theorem eq_487 (X : Matrix m m R) (n : ℕ) (hx : (X - 1).det ≠ 0) :
    (X ^ n - 1) * (X - 1)⁻¹ = ∑ i in Finset.range n, X ^ i := by
  rw [← geom_sum_mul X n, mul_nonsing_inv_cancel_right _ _ hx.isUnit]

/-! #### Taylor Expansion of Scalar Function -/


/-! #### Matrix Functions by Infinite Series -/


/-! #### Identity and commutations -/


/-! #### Exponential Matrix Function -/

section
open NormedSpace

theorem eq_494 (A : Matrix n n ℝ) : exp ℝ A = ∑' n : ℕ, (n !⁻¹ : ℝ) • A ^ n := by rw [exp_eq_tsum]

theorem eq_495 (A : Matrix n n ℝ) : exp ℝ (-A) = ∑' n : ℕ, (n !⁻¹ : ℝ) • (-1 : Matrix _ _ ℝ) ^ n * A ^ n := by
  simp_rw [exp_eq_tsum, neg_pow A, smul_mul_assoc]

theorem eq_496 (t : ℝ) (A : Matrix n n ℝ) : exp ℝ (t • A) = ∑' n : ℕ, (n !⁻¹ : ℝ) • t ^ (n : ℕ) • A ^ n := by simp_rw [exp_eq_tsum, smul_pow]

theorem eq_498 (A B : Matrix n n ℝ) (h : A * B = B * A) : exp ℝ A * exp ℝ B = exp ℝ (A + B) :=
  (exp_add_of_commute _ _ _ h).symm

theorem eq_499 (A : Matrix n n ℝ) : (exp ℝ A)⁻¹ = exp ℝ (-A) :=
  (exp_neg _ _).symm

end

/-! ### Kronecker and vec Operator -/


/-! #### The Kronecker Product -/


open scoped Kronecker

theorem eq_505 (A : Matrix m n R) (B : Matrix r q R) :
    A ⊗ₖ B = Matrix.of fun i j : _ × _ => (A i.1 j.1 • B) i.2 j.2 :=
  rfl

theorem eq_506 (A : Matrix m n R) (B C : Matrix r q R) : A ⊗ₖ (B + C) = A ⊗ₖ B + A ⊗ₖ C :=
  kronecker_add _ _ _

theorem eq_507 [Nontrivial m] [Nonempty n] :
    ¬∀ (A : Matrix m n R) (B : Matrix m n R), A ⊗ₖ B = B ⊗ₖ A := by
  intro h
  obtain ⟨m1, m2, hm⟩ := exists_pair_ne m
  obtain ⟨n1⟩ := id ‹Nonempty n›
  let A := stdBasisMatrix m1 n1 (1 : R)
  let B := stdBasisMatrix m2 n1 (1 : R)
  have := Matrix.ext_iff.mpr (h A B) (m1, m2) (n1, n1)
  simp [StdBasisMatrix.apply_same, StdBasisMatrix.apply_of_row_ne hm,
    mul_zero, mul_one, one_ne_zero] at this

/-- Note we have to "cast" between the types -/
theorem eq_508 (A : Matrix m n R) (B : Matrix r q R) (C : Matrix l p R) :
    A ⊗ₖ (B ⊗ₖ C) = reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _) (A ⊗ₖ B ⊗ₖ C) :=
  (kronecker_assoc _ _ _).symm

theorem eq_509 (a b : R) (A : Matrix m n R) (B : Matrix r q R) :
    (a • A) ⊗ₖ (b • B) = (a * b) • A ⊗ₖ B := by rw [smul_kronecker, kronecker_smul, smul_smul]

theorem eq_510 (A : Matrix m n R) (B : Matrix r q R) : (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ := by
  rw [kroneckerMap_transpose]

theorem eq_511 (A : Matrix l m R) (B : Matrix p q R) (C : Matrix m n R) (D : Matrix q r R) :
    A ⊗ₖ B * C ⊗ₖ D = (A * C) ⊗ₖ (B * D) := by rw [Matrix.mul_kronecker_mul]

theorem eq_512 (A : Matrix m m R) (B : Matrix n n R) : (A ⊗ₖ B)⁻¹ = A⁻¹ ⊗ₖ B⁻¹ :=
  inv_kronecker _ _

-- lemma eq_513 : sorry := sorry

lemma eq_514 (A : Matrix l m R) (B : Matrix p q R) : rank (A ⊗ₖ B) = rank A * rank B := sorry

theorem eq_515 (A : Matrix m m R) (B : Matrix n n R) : trace (A ⊗ₖ B) = trace A * trace B := by
  simp_rw [Matrix.trace, Matrix.diag, Finset.sum_mul, Finset.mul_sum, ← Finset.univ_product_univ,
    Finset.sum_product, kronecker_apply]

theorem eq_516 (A : Matrix m m R) (B : Matrix n n R) :
    det (A ⊗ₖ B) = det A ^ Fintype.card n * det B ^ Fintype.card m :=
  det_kronecker _ _

lemma eq_517 : sorry := sorry
lemma eq_518 : sorry := sorry
lemma eq_519 : sorry := sorry

/-! #### The Vec Operator -/

def vec (A : Matrix m n R) : Matrix (n × m) Unit R :=
  col fun ij => A ij.2 ij.1

theorem eq_520 (A : Matrix l m R) (X : Matrix m n R) (B : Matrix n p R) :
    vec (A * X * B) = Bᵀ ⊗ₖ A * vec X := by
  ext ⟨k, l⟩
  simp_rw [vec, Matrix.mul_apply, Matrix.kroneckerMap_apply, col_apply, Finset.sum_mul,
    transpose_apply, ← Finset.univ_product_univ, Finset.sum_product, mul_right_comm _ _ (B _ _),
    mul_comm _ (B _ _)]

theorem eq_521 (A B : Matrix m n R) : (Aᵀ * B).trace = ((vec A)ᵀ * vec B) () () := by
  simp_rw [Matrix.trace, Matrix.diag, Matrix.mul_apply, vec, transpose_apply, col_apply, ←
    Finset.univ_product_univ, Finset.sum_product]

theorem eq_522 (A B : Matrix m n R) : vec (A + B) = vec A + vec B :=
  rfl

theorem eq_523 (r : R) (A : Matrix m n R) : vec (r • A) = r • vec A :=
  rfl

-- note: `Bᵀ` is `B` in the PDF
theorem eq_524 (a : m → R) (X : Matrix m n R) (B : Matrix n n R) (c : m → R) :
    row a * X * B * Xᵀ * col c = (vec X)ᵀ * Bᵀ ⊗ₖ (col c * row a) * vec X := by
  -- not the proof from the book
  ext ⟨i, j⟩
  simp only [vec, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Matrix.kroneckerMap_apply,
    transpose_apply, Matrix.row_apply, Matrix.col_apply, Fintype.sum_unique]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product, @Finset.sum_comm _ m n]
  rw [Finset.sum_comm]
  refine' Finset.sum_congr rfl fun k _ => _
  refine' Finset.sum_congr rfl fun l _ => _
  rw [Finset.sum_comm]
  refine' Finset.sum_congr rfl fun kk _ => _
  refine' Finset.sum_congr rfl fun ll _ => _
  ring

/-! ### Vector Norms -/


/-! #### Examples -/


theorem eq_525 (x : n → ℂ) : ‖(WithLp.equiv 1 _).symm x‖ = ∑ i, Complex.abs (x i) := by
  simpa using PiLp.norm_eq_of_nat 1 Nat.cast_one.symm ((WithLp.equiv 1 _).symm x)

theorem eq_526 (x : n → ℂ) : ↑(‖(WithLp.equiv 2 _).symm x‖ ^ 2 : ℝ) = star x ⬝ᵥ x := by
  rw [← EuclideanSpace.inner_piLp_equiv_symm, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
  rfl  -- porting note: added

theorem eq_527 (x : n → ℂ) (p : ℝ≥0∞) (h : 0 < p.toReal) :
    ‖(WithLp.equiv p _).symm x‖ = (∑ i, Complex.abs (x i) ^ p.toReal) ^ (1 / p.toReal) := by
  simp_rw [PiLp.norm_eq_sum h, WithLp.equiv_symm_pi_apply, Complex.norm_eq_abs]

theorem eq_528 (x : n → ℂ) : ‖(WithLp.equiv ∞ _).symm x‖ = ⨆ i, Complex.abs (x i) := by
  simp_rw [PiLp.norm_eq_ciSup, WithLp.equiv_symm_pi_apply, Complex.norm_eq_abs]

/-! ### Matrix Norms -/


/-! #### Definitions -/


section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem eq_529 (A : Matrix n n ℝ) : 0 ≤ ‖A‖ :=
  norm_nonneg _

theorem eq_530 (A : Matrix n n ℝ) : ‖A‖ = 0 ↔ A = 0 :=
  norm_eq_zero

theorem eq_531 (r : ℝ) (A : Matrix n n ℝ) : ‖r • A‖ = |r| * ‖A‖ := by
  rw [norm_smul r A, Real.norm_eq_abs]

theorem eq_532 (A B : Matrix n n ℝ) : ‖A + B‖ ≤ ‖A‖ + ‖B‖ :=
  norm_add_le _ _

end

/-! #### Induced Norm or Operator Norm -/


-- we just use one of the norms as an example; there is no generalization available
section

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

lemma eq_533 (A : Matrix m n ℝ) : ‖A‖ = sSup { ‖A.mulVec x‖ | (x) (hx : ‖x‖ = 1)} := by
  suffices ‖A‖ = sSup ((‖A.mulVec ·‖) '' Metric.sphere 0 1) by
    simpa [Set.image, mem_sphere_zero_iff_norm] using this
  simp_rw [linfty_opNorm_eq_opNorm]
  -- this is not quite the right lemma
  rw [←ContinuousLinearMap.sSup_unit_ball_eq_norm]
  sorry

theorem eq_534 [Nonempty n] : ‖(1 : Matrix n n ℝ)‖ = 1 :=
  norm_one

theorem eq_535 (A : Matrix m n ℝ) (x : n → ℝ) : ‖A.mulVec x‖ ≤ ‖A‖ * ‖x‖ :=
  linfty_opNorm_mulVec _ _

theorem eq_536 (A : Matrix m n ℝ) (B : Matrix n p ℝ) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ :=
  linfty_opNorm_mul _ _

end

/-! #### Examples -/


lemma eq_537 (A : Matrix m n ℝ) : sorry = ⨆ j, ∑ i, ‖A i j‖ := sorry

-- lemma eq_538 : sorry := sorry
-- lemma eq_539 : sorry := sorry
section

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace

theorem eq_540 (A : Matrix m n ℝ) : ‖A‖ = ↑(Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) := by
  rw [linfty_opNorm_def]

end

section

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem eq_541 (A : Matrix m n ℝ) : ‖A‖ = Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) := by
  rw [frobenius_norm_def, Real.sqrt_eq_rpow]

end

section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem eq_542 (A : Matrix m n ℝ) : ‖A‖ = ↑(Finset.univ.sup fun ij : _ × _ => ‖A ij.1 ij.2‖₊) := by
  simp_rw [← Finset.univ_product_univ, Finset.sup_product_left, ← Pi.nnnorm_def, coe_nnnorm]

end

/-! #### Inequalities -/


/-! #### Condition Number -/


/-! ### Rank -/


/-! #### Sylvester’s Inequality -/


-- lemma eq_543 : sorry := sorry
lemma eq_544 (A : Matrix m n ℝ) :
    letI m' := Fintype.card m
    letI n' := Fintype.card n
    letI d := A.rank
    let norms : Fin 6 → (Matrix m n ℝ → ℝ) := sorry
    let coeffs : Matrix _ _ ℝ := !![
      1,                   1,              1,              1,        1,        1;
      m',                  1,              m',             .sqrt m', .sqrt m', .sqrt m';
      n',                  n',             1,              .sqrt n', .sqrt n', .sqrt n';
      .sqrt (m' * n'),     .sqrt n',       .sqrt m',       1,        1,        1;
      .sqrt (m' * n'),     .sqrt n',       .sqrt m',       .sqrt d,  1,        1;
      .sqrt (m' * n' * d), .sqrt (n' * d), .sqrt (m' * d), d,        .sqrt d,  1]
    ∀ i j, norms i A ≤ coeffs i j * norms j A := sorry


-- lemma eq_545 : sorry := sorry
theorem eq_546 (A : Matrix m n ℝ) (B : Matrix n r ℝ) :
    rank A + rank B - Fintype.card n ≤ rank (A * B) ∧ rank (A * B) ≤ min (rank A) (rank B) :=
  ⟨sorry, rank_mul_le _ _⟩

/-! ### Integral Involving Dirac Delta Functions -/


/-! ### Miscellaneous -/


-- lemma eq_547 : sorry := sorry
-- lemma eq_548 : sorry := sorry
theorem eq_549 (A : Matrix m n ℝ) :
    A.rank = Aᵀ.rank ∧ A.rank = (A * Aᵀ).rank ∧ A.rank = (Aᵀ * A).rank :=
  ⟨A.rank_transpose.symm, A.rank_self_mul_transpose.symm, A.rank_transpose_mul_self.symm⟩

theorem eq_550 (A : Matrix m m ℝ) :
    A.PosDef ↔ ∃ B : (Matrix m m ℝ)ˣ, A = (↑B : Matrix m m ℝ) * ↑Bᵀ :=
  sorry

end MatrixCookbook
