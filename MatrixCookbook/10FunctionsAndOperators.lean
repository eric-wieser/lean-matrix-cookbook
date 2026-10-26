module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import MatrixCookbook.ForMathlib.Analysis.CStarAlgebra.Matrix
public import MatrixCookbook.ForMathlib.Analysis.Matrix.Spectrum

/-! # Functions and Operators -/

@[expose] public section

variable {ι : Type*} {R : Type*} {l m n p q r : Type*}

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
    (X ^ n - 1) * (X - 1)⁻¹ = ∑ i ∈ Finset.range n, X ^ i := by
  rw [← geom_sum_mul X n, mul_nonsing_inv_cancel_right _ _ hx.isUnit]

/-! #### Taylor Expansion of Scalar Function -/


/-! #### Matrix Functions by Infinite Series -/


/-! #### Identity and commutations -/


/-! #### Exponential Matrix Function -/

section
open NormedSpace

theorem eq_494 (A : Matrix n n ℝ) : exp A = ∑' n : ℕ, (n !⁻¹ : ℝ) • A ^ n := by rw [exp_eq_tsum ℝ]

theorem eq_495 (A : Matrix n n ℝ) : exp (-A) = ∑' n : ℕ, (n !⁻¹ : ℝ) • (-1 : Matrix _ _ ℝ) ^ n * A ^ n := by
  simp_rw [exp_eq_tsum ℝ, neg_pow A, smul_mul_assoc]

theorem eq_496 (t : ℝ) (A : Matrix n n ℝ) : exp (t • A) = ∑' n : ℕ, (n !⁻¹ : ℝ) • t ^ (n : ℕ) • A ^ n := by simp_rw [exp_eq_tsum ℝ, smul_pow]

theorem eq_498 (A B : Matrix n n ℝ) (h : A * B = B * A) : exp A * exp B = exp (A + B) :=
  (Matrix.exp_add_of_commute A B h).symm

theorem eq_499 (A : Matrix n n ℝ) : (exp A)⁻¹ = exp (-A) :=
  (Matrix.exp_neg A).symm

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
  let A := single m1 n1 (1 : R)
  let B := single m2 n1 (1 : R)
  have := Matrix.ext_iff.mpr (h A B) (m1, m2) (n1, n1)
  simp [single_apply_same, single_apply_of_row_ne hm,
    mul_zero, mul_one, one_ne_zero, A, B] at this

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

lemma eq_513 : (sorry : Prop) := sorry

lemma eq_514 (A : Matrix l m R) (B : Matrix p q R) : rank (A ⊗ₖ B) = rank A * rank B := sorry

theorem eq_515 (A : Matrix m m R) (B : Matrix n n R) : trace (A ⊗ₖ B) = trace A * trace B :=
  trace_kronecker _ _

theorem eq_516 (A : Matrix m m R) (B : Matrix n n R) :
    det (A ⊗ₖ B) = det A ^ Fintype.card n * det B ^ Fintype.card m :=
  det_kronecker _ _

lemma eq_517 : (sorry : Prop) := sorry
lemma eq_518 : (sorry : Prop) := sorry
lemma eq_519 : (sorry : Prop) := sorry

/-! #### The Vec Operator -/

theorem eq_520 (A : Matrix l m R) (X : Matrix m n R) (B : Matrix n p R) :
    vec (A * X * B) = Bᵀ ⊗ₖ A *ᵥ vec X := by
  rw [kronecker_mulVec_vec, transpose_transpose]

theorem eq_521 (A B : Matrix m n R) : (Aᵀ * B).trace = (vec A ⬝ᵥ vec B) :=
  (vec_dotProduct_vec _ _).symm

theorem eq_522 (A B : Matrix m n R) : vec (A + B) = vec A + vec B := vec_add _ _

theorem eq_523 (r : R) (A : Matrix m n R) : vec (r • A) = r • vec A := vec_smul _ _

-- note: `Bᵀ` is `B` in the PDF
theorem eq_524 (a : m → R) (X : Matrix m n R) (B : Matrix n n R) (c : m → R) :
    a ᵥ* (X * B * Xᵀ) ⬝ᵥ c = vec X ᵥ* (Bᵀ ⊗ₖ vecMulVec c a) ⬝ᵥ vec X := by
  -- not the proof from the book
  simp only [vec, dotProduct, vecMul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Matrix.kroneckerMap_apply,
    transpose_apply]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product, @Finset.sum_comm n _ m, vecMulVec,
    of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun kk _ => ?_
  refine Finset.sum_congr rfl fun ll _ => ?_
  ring

/-! ### Vector Norms -/


/-! #### Examples -/


theorem eq_525 (x : n → ℂ) : ‖WithLp.toLp 1 x‖ = ∑ i, ‖x i‖ := by
  simpa using PiLp.norm_eq_of_nat 1 Nat.cast_one.symm (WithLp.toLp 1 x)

theorem eq_526 (x : n → ℂ) : ↑(‖WithLp.toLp 2 x‖ ^ 2 : ℝ) = star x ⬝ᵥ x := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp, inner_self_eq_norm_sq_to_K,
    Complex.ofReal_pow]
  rfl

theorem eq_527 (x : n → ℂ) (p : ℝ≥0∞) (h : 0 < p.toReal) :
    ‖WithLp.toLp p x‖ = (∑ i, ‖x i‖ ^ p.toReal) ^ (1 / p.toReal) := by
  simp_rw [PiLp.norm_eq_sum h]

theorem eq_528 (x : n → ℂ) : ‖WithLp.toLp ∞ x‖ = ⨆ i, ‖x i‖ := by
  simp_rw [PiLp.norm_eq_ciSup]

/-! ### Matrix Norms -/


/-! #### Definitions -/


theorem eq_529 (A : Matrix n n ℝ) : open scoped Matrix.Norms.Elementwise in 0 ≤ ‖A‖ :=
  open scoped Matrix.Norms.Elementwise in norm_nonneg _

theorem eq_530 (A : Matrix n n ℝ) : open scoped Matrix.Norms.Elementwise in ‖A‖ = 0 ↔ A = 0 :=
  open scoped Matrix.Norms.Elementwise in norm_eq_zero

theorem eq_531 (r : ℝ) (A : Matrix n n ℝ) :
    open scoped Matrix.Norms.Elementwise in ‖r • A‖ = |r| * ‖A‖ := by
  open scoped Matrix.Norms.Elementwise in rw [norm_smul r A, Real.norm_eq_abs]

theorem eq_532 (A B : Matrix n n ℝ) : open scoped Matrix.Norms.Elementwise in ‖A + B‖ ≤ ‖A‖ + ‖B‖ :=
  open scoped Matrix.Norms.Elementwise in norm_add_le _ _

/-! #### Induced Norm or Operator Norm -/


-- we just use one of the norms as an example; there is no generalization available
section

open scoped Matrix.Norms.Operator

lemma eq_533 (A : Matrix m n ℝ) : ‖A‖ = sSup { ‖A.mulVec x‖ | (x) (_ : ‖x‖ = 1)} := by
  suffices ‖A‖ = sSup ((‖A.mulVec ·‖) '' Metric.sphere 0 1) by
    simpa [Set.image, mem_sphere_zero_iff_norm] using this
  simp_rw [linfty_opNorm_eq_opNorm, ← ContinuousLinearMap.sSup_sphere_eq_norm]
  simp

theorem eq_534 [Nonempty n] : ‖(1 : Matrix n n ℝ)‖ = 1 :=
  norm_one

theorem eq_535 (A : Matrix m n ℝ) (x : n → ℝ) : ‖A.mulVec x‖ ≤ ‖A‖ * ‖x‖ :=
  linfty_opNorm_mulVec _ _

theorem eq_536 (A : Matrix m n ℝ) (B : Matrix n p ℝ) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ :=
  linfty_opNorm_mul _ _

end

/-! #### Examples -/


lemma eq_537 (A : Matrix m n ℝ) : sorry = ⨆ j, ∑ i, ‖A i j‖ := sorry

lemma eq_538 (A : Matrix m n ℝ) :
    (open scoped Matrix.Norms.L2Operator in ‖A‖) =
      NNReal.sqrt (Finset.univ.sup fun i => ⟨_, A.eigenvalues_conjTranspose_mul_self_nonneg i⟩) := sorry

lemma eq_539 : (sorry : Prop) := sorry

theorem eq_540 (A : Matrix m n ℝ) :
    (open scoped Matrix.Norms.Operator in ‖A‖) =
      ↑(Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) := by
  rw [linfty_opNorm_def]

theorem eq_541 (A : Matrix m n ℝ) :
    (open scoped Matrix.Norms.Frobenius in ‖A‖) =
      Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) := by
  rw [frobenius_norm_def, Real.sqrt_eq_rpow]

theorem eq_542 (A : Matrix m n ℝ) :
    (open scoped Matrix.Norms.Elementwise in ‖A‖) =
      ↑(Finset.univ.sup fun ij : _ × _ => ‖A ij.1 ij.2‖₊) := by
  open scoped Matrix.Norms.Elementwise in
  rw [← coe_nnnorm, Matrix.nnnorm_def, Pi.nnnorm_def, ← Finset.univ_product_univ,
    Finset.sup_product_left]
  simp_rw [Pi.nnnorm_def]

lemma eq_543 : (sorry : Prop) := sorry

/-! #### Inequalities -/

-- TODO: are the bounds tight?
lemma eq_544 (A : Matrix m n ℝ) :
    letI m' := Fintype.card m
    letI n' := Fintype.card n
    letI d := A.rank
    let norms : Fin 6 → (Matrix m n ℝ → ℝ) := ![
      open scoped Norms.Elementwise in (‖·‖),
      sorry, -- L1 norm
      open scoped Norms.Operator in (‖·‖),
      open scoped Norms.L2Operator in (‖·‖),
      open scoped Norms.Frobenius in (‖·‖),
      sorry -- Ky Fan norm
    ]
    let coeffs : Matrix _ _ ℝ := !![
      1,                   1,              1,              1,        1,        1;
      m',                  1,              m',             .sqrt m', .sqrt m', .sqrt m';
      n',                  n',             1,              .sqrt n', .sqrt n', .sqrt n';
      .sqrt (m' * n'),     .sqrt n',       .sqrt m',       1,        1,        1;
      .sqrt (m' * n'),     .sqrt n',       .sqrt m',       .sqrt d,  1,        1;
      .sqrt (m' * n' * d), .sqrt (n' * d), .sqrt (m' * d), d,        .sqrt d,  1]
    ∀ i j, norms i A ≤ coeffs i j * norms j A := by
  -- unpack the matrix into the elements
  simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, and_true, Matrix.of_apply, Fin.reduceSucc,
    cons_val, one_mul]
  -- the diagonal elements are easy; `?a_b` is the goal `‖A‖_a ≤ c * ‖A‖_b`
  refine ⟨⟨le_rfl, ?max_l1, ?max_linf, ?max_l2, ?max_frob, ?max_kf⟩,
    ⟨?l1_max, le_rfl, ?l1_linf, ?l1_l2, ?l1_frob, ?l1_kf⟩,
    ⟨?linf_max, ?linf_l1, le_rfl, ?linf_l2, ?linf_frob, ?linf_kf⟩,
    ⟨?l2_max, ?l2_l1, ?l2_linf, le_rfl, ?l2_frob, ?l2_kf⟩,
    ⟨?frob_max, ?frob_l1, ?frob_linf, ?frob_l2, le_rfl, ?frob_kf⟩,
    ⟨?kf_max, ?kf_l1, ?kf_linf, ?kf_l2, ?kf_frob, le_rfl⟩⟩
  case max_linf => exact norm_le_linfty_opNorm A
  case max_l2 => exact norm_le_l2_opNorm A
  case max_frob => exact norm_le_frobenius_norm A
  case linf_max => simpa [nsmul_eq_mul] using linfty_opNorm_le_card_nsmul_norm A
  case linf_l2 => exact linfty_opNorm_le_sqrt_card_mul_l2_opNorm A
  case linf_frob => exact linfty_opNorm_le_sqrt_card_mul_frobenius_norm A
  case l2_max => simpa using l2_opNorm_le_sqrt_card_mul_norm A
  case l2_linf => exact l2_opNorm_le_sqrt_card_mul_linfty_opNorm A
  case l2_frob => exact l2_opNorm_le_frobenius_norm A
  case frob_max => simpa using frobenius_norm_le_sqrt_card_mul_norm A
  case frob_linf => exact frobenius_norm_le_sqrt_card_mul_linfty_opNorm A
  case frob_l2 => exact frobenius_norm_le_sqrt_rank_mul_l2_opNorm A
  -- the remaining 18 goals all involve the L1 or Ky Fan norms, which are not yet defined
  all_goals sorry



/-! #### Condition Number -/

open scoped Matrix.Norms.L2Operator in
lemma eq_545 (A : Matrix n n ℝ) : ‖A‖ * ‖A⁻¹‖ = sorry / sorry := sorry

/-! ### Rank -/

/-! #### Sylvester’s Inequality -/

theorem eq_546 (A : Matrix m n ℝ) (B : Matrix n r ℝ) :
    rank A + rank B - Fintype.card n ≤ rank (A * B) ∧ rank (A * B) ≤ min (rank A) (rank B) :=
  ⟨tsub_le_iff_right.mpr (rank_mul_ge A B), rank_mul_le _ _⟩

/-! ### Integral Involving Dirac Delta Functions -/


/-! ### Miscellaneous -/


lemma eq_547 : (sorry : Prop) := sorry
lemma eq_548 : (sorry : Prop) := sorry

theorem eq_549 (A : Matrix m n ℝ) :
    A.rank = Aᵀ.rank ∧ A.rank = (A * Aᵀ).rank ∧ A.rank = (Aᵀ * A).rank :=
  ⟨A.rank_transpose.symm, A.rank_self_mul_transpose.symm, A.rank_transpose_mul_self.symm⟩

open scoped MatrixOrder Matrix.Norms.L2Operator in
theorem eq_550 (A : Matrix m m ℝ) :
    A.PosDef ↔ ∃ B : Matrix m m ℝ, IsUnit B ∧ A = B * Bᵀ := by
  rw [← isStrictlyPositive_iff_posDef, CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self,
    (Function.RightInverse.surjective transpose_transpose).exists]
  simp [isUnit_transpose, star_eq_conjTranspose]

end MatrixCookbook
