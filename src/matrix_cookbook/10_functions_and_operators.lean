import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.trace
import data.real.nnreal
import topology.metric_space.basic
import data.matrix.notation
import ring_theory.power_series.basic
import analysis.normed_space.matrix_exponential
import data.matrix.kronecker
import data.matrix.rank
import linear_algebra.matrix.pos_def
import analysis.inner_product_space.pi_L2

/-! # Functions and Operators -/

variables {ι : Type*} {R : Type*} {l m n p q r : Type*}
variables [fintype l] [fintype m] [fintype n] [fintype p] [fintype q] [fintype r]
variables [decidable_eq l] [decidable_eq m] [decidable_eq n] [decidable_eq p] [decidable_eq q] [decidable_eq r]

open_locale nat big_operators matrix nnreal ennreal
open matrix

namespace matrix_cookbook

variables [field R]

/-! ### Functions and Series -/

/-! #### Finite Series -/

/-- The pdf does not mention `hx`! -/
lemma eq_487 (X : matrix m m R) (n : ℕ) (hx : (X - 1).det ≠ 0):
  (X ^ n - 1) * (X - 1)⁻¹ = ∑ i in finset.range n, X^i :=
by rw [←geom_sum_mul X n, matrix.mul_eq_mul, matrix.mul_eq_mul,
    mul_nonsing_inv_cancel_right _ _ hx.is_unit]

/-! #### Taylor Expansion of Scalar Function -/


/-! #### Matrix Functions by Infinite Series -/

/-! #### Identity and commutations -/

/-! #### Exponential Matrix Function -/

lemma eq_494 (A : matrix n n ℝ) : exp ℝ A = ∑' n : ℕ, (n!⁻¹ : ℝ) • A ^ n :=
by rw exp_eq_tsum

lemma eq_495 (A : matrix n n ℝ) : exp ℝ (-A) = ∑' n : ℕ, (n!⁻¹ : ℝ) • (-1)^n * A ^ n :=
by simp_rw [exp_eq_tsum, neg_pow A, smul_mul_assoc]

lemma eq_496 (t : ℝ) (A : matrix n n ℝ) : exp ℝ (t • A) = ∑' n : ℕ, (n!⁻¹ : ℝ) • t ^ n • A ^ n :=
by simp_rw [exp_eq_tsum, smul_pow]

lemma eq_498 (A B : matrix n n ℝ) (h : A * B = B * A) : exp ℝ A * exp ℝ B = exp ℝ (A + B) :=
(exp_add_of_commute _ _ _ h).symm

lemma eq_499 (A : matrix n n ℝ) : (exp ℝ A)⁻¹ = exp ℝ (-A) :=
(exp_neg _ _).symm

/-! ### Kronecker and vec Operator -/

/-! #### The Kronecker Product -/
open_locale kronecker

lemma eq_505 (A : matrix m n R) (B : matrix r q R) :
  A ⊗ₖ B = matrix.of (λ i j : _ × _, (A i.1 j.1 • B) i.2 j.2) := rfl

lemma eq_506 (A : matrix m n R) (B C : matrix r q R) : A ⊗ₖ (B + C) = A ⊗ₖ B + A ⊗ₖ C :=
kronecker_add _ _ _

lemma eq_507 [nontrivial m] [nonempty n]:
  ¬∀ (A : matrix m n R) (B : matrix m n R), A ⊗ₖ B = B ⊗ₖ A :=
begin
  intro h,
  obtain ⟨m1, m2, hm⟩ := exists_pair_ne m,
  obtain ⟨n1⟩ := id ‹nonempty n›,
  let A := std_basis_matrix m1 n1 (1 : R),
  let B := std_basis_matrix m2 n1 (1 : R),
  have := matrix.ext_iff.mpr (h A B) (m1, m2) (n1, n1),
  simpa [A, B, std_basis_matrix.apply_same, std_basis_matrix.apply_of_row_ne hm, mul_zero, mul_one,
    one_ne_zero] using this,
end

/-- Note we have to "cast" between the types -/
lemma eq_508 (A : matrix m n R) (B : matrix r q R) (C : matrix l p R) :
  A ⊗ₖ (B ⊗ₖ C) = reindex (equiv.prod_assoc _ _ _) (equiv.prod_assoc _ _ _)
    ((A ⊗ₖ B) ⊗ₖ C) :=
(kronecker_assoc _ _ _).symm

lemma eq_509 (a b : R) (A : matrix m n R) (B : matrix r q R) :
  (a • A) ⊗ₖ (b • B) = (a*b) • (A ⊗ₖ B) :=
by rw [smul_kronecker, kronecker_smul, smul_smul]

lemma eq_510 (A : matrix m n R) (B : matrix r q R) :
  (A ⊗ₖ B)ᵀ = (Aᵀ ⊗ₖ Bᵀ) :=
by rw [kronecker_map_transpose]

lemma eq_511 (A : matrix l m R) (B : matrix p q R) (C : matrix m n R) (D : matrix q r R) :
  (A ⊗ₖ B) ⬝ (C ⊗ₖ D) = (A ⬝ C) ⊗ₖ (B ⬝ D) :=
by rw matrix.mul_kronecker_mul

lemma eq_512 (A : matrix m m R) (B : matrix n n R) :
  (A ⊗ₖ B)⁻¹ = (A⁻¹ ⊗ₖ B⁻¹) :=
inv_kronecker _ _

-- lemma eq_513 : sorry := sorry
-- lemma eq_514 : sorry := sorry

lemma eq_515 (A : matrix m m R) (B : matrix n n R) :
  trace (A ⊗ₖ B) = trace A * trace B :=
by simp_rw [matrix.trace, matrix.diag, finset.sum_mul, finset.mul_sum,
    ←finset.univ_product_univ, finset.sum_product, kronecker_apply]

lemma eq_516 (A : matrix m m R) (B : matrix n n R) :
  det (A ⊗ₖ B) = det A ^ fintype.card n * det B ^ fintype.card m :=
det_kronecker _ _

-- lemma eq_517 : sorry := sorry
-- lemma eq_518 : sorry := sorry
-- lemma eq_519 : sorry := sorry

/-! #### The Vec Operator -/

def vec (A : matrix m n R) : matrix (n × m) unit R :=
col (λ ij, A ij.2 ij.1)

lemma eq_520 (A : matrix l m R) (X : matrix m n R) (B : matrix n p R) :
  vec (A ⬝ X ⬝ B) = (Bᵀ ⊗ₖ A) ⬝ vec X :=
begin
  ext ⟨k, l⟩,
  simp_rw [vec, matrix.mul_apply, matrix.kronecker_map_apply, col_apply, finset.sum_mul,
    transpose_apply, ←finset.univ_product_univ, finset.sum_product, mul_right_comm _ _ (B _ _),
      mul_comm _ (B _ _)],
end
lemma eq_521 (A B : matrix m n R) : (Aᵀ ⬝ B).trace = ((vec A)ᵀ ⬝ vec B) () () :=
by simp_rw [matrix.trace, matrix.diag, matrix.mul_apply, vec, transpose_apply, col_apply,
    ←finset.univ_product_univ, finset.sum_product]
lemma eq_522 (A B : matrix m n R) : vec (A + B) = vec A + vec B := rfl
lemma eq_523 (r : R) (A : matrix m n R) : vec (r • A) = r • vec A := rfl

-- note: `Bᵀ` is `B` in the PDF
lemma eq_524 (a : m → R) (X : matrix m n R) (B : matrix n n R) (c : m → R) :
  row a ⬝ X ⬝ B ⬝ Xᵀ ⬝ col c = (vec X)ᵀ ⬝ (Bᵀ ⊗ₖ (col c ⬝ row a)) ⬝ vec X :=
begin
  -- not the proof from the book
  ext ⟨i, j⟩,
  simp only [vec, matrix.mul_apply, finset.sum_mul, finset.mul_sum,
    matrix.kronecker_map_apply, transpose_apply, matrix.row_apply, matrix.col_apply,
    fintype.sum_unique],
  simp_rw [←finset.univ_product_univ, finset.sum_product, @finset.sum_comm _ m n],
  rw finset.sum_comm,
  refine finset.sum_congr rfl (λ k _, _),
  refine finset.sum_congr rfl (λ l _, _),
  rw finset.sum_comm,
  refine finset.sum_congr rfl (λ kk _, _),
  refine finset.sum_congr rfl (λ ll _, _),
  ring,
end

/-! ### Vector Norms -/

/-! #### Examples -/

lemma eq_525 (x : n → ℂ) : ‖(pi_Lp.equiv 1 _).symm x‖ = ∑ i, complex.abs (x i) :=
by simpa using pi_Lp.norm_eq_of_nat 1 (nat.cast_one.symm) ((pi_Lp.equiv 1 _).symm x)

lemma eq_526 (x : n → ℂ) : ↑(‖(pi_Lp.equiv 2 _).symm x‖^2) = star x ⬝ᵥ x :=
by rw [←euclidean_space.inner_pi_Lp_equiv_symm, inner_self_eq_norm_sq_to_K, complex.of_real_pow]

lemma eq_527 (x : n → ℂ) (p : ℝ≥0∞) (h : 0 < p.to_real) :
  ‖(pi_Lp.equiv p _).symm x‖ = (∑ i, complex.abs (x i) ^ p.to_real)^(1/p.to_real) :=
by simp_rw [pi_Lp.norm_eq_sum h, pi_Lp.equiv_symm_apply, complex.norm_eq_abs]

lemma eq_528 (x : n → ℂ) :
  ‖(pi_Lp.equiv ∞ _).symm x‖ = ⨆ i, complex.abs (x i) :=
by simp_rw [pi_Lp.norm_eq_csupr, pi_Lp.equiv_symm_apply, complex.norm_eq_abs]

/-! ### Matrix Norms -/

/-! #### Definitions -/
section
local attribute [instance] matrix.normed_add_comm_group matrix.normed_space

lemma eq_529 (A : matrix n n ℝ) : 0 ≤ ‖A‖ := norm_nonneg _
lemma eq_530 (A : matrix n n ℝ) : ‖A‖ = 0 ↔ A = 0 := norm_eq_zero
lemma eq_531 (r : ℝ) (A : matrix n n ℝ) : ‖r • A‖ = |r| * ‖A‖ := by rw [norm_smul r A, real.norm_eq_abs]
lemma eq_532 (A B : matrix n n ℝ) : ‖A + B‖ ≤ ‖A‖ + ‖B‖ := norm_add_le _ _

end

/-! #### Induced Norm or Operator Norm -/

-- lemma eq_533 : sorry := sorry

-- we just use one of the norms as an example; there is no generalization available
section
local attribute [instance] matrix.linfty_op_normed_add_comm_group matrix.linfty_op_normed_space
local attribute [instance] matrix.linfty_op_normed_ring matrix.linfty_op_normed_algebra
local attribute [instance] matrix.linfty_op_norm_one_class
lemma eq_534 [nonempty n] : ‖(1 : matrix n n ℝ)‖ = 1 := norm_one
lemma eq_535 (A : matrix m n ℝ) (x : n → ℝ) : ‖A.mul_vec x‖ ≤ ‖A‖ * ‖x‖ :=
linfty_op_norm_mul_vec _ _
lemma eq_536 (A : matrix m n ℝ) (B : matrix n p ℝ) : ‖A⬝B‖ ≤ ‖A‖ * ‖B‖ :=
linfty_op_norm_mul _ _
end

/-! #### Examples -/


-- lemma eq_537 : sorry := sorry
-- lemma eq_538 : sorry := sorry
-- lemma eq_539 : sorry := sorry

section
local attribute [instance] matrix.linfty_op_normed_add_comm_group matrix.linfty_op_normed_space
lemma eq_540 (A : matrix m n ℝ) : ‖A‖ = ↑(finset.univ.sup (λ i, ∑ j, ‖A i j‖₊)) :=
by rw [linfty_op_norm_def]
end

section
local attribute [instance] matrix.frobenius_normed_add_comm_group matrix.frobenius_normed_space
lemma eq_541 (A : matrix m n ℝ) : ‖A‖ = real.sqrt (∑ i j, ‖A i j‖ ^ (2 : ℝ)) :=
by rw [frobenius_norm_def, real.sqrt_eq_rpow]
end

section
local attribute [instance] matrix.normed_add_comm_group matrix.normed_space
lemma eq_542 (A : matrix m n ℝ) : ‖A‖ = ↑(finset.univ.sup (λ ij : _ × _, ‖A ij.1 ij.2‖₊)) :=
by simp_rw [←finset.univ_product_univ, finset.sup_product_left, ←pi.nnnorm_def, coe_nnnorm]
end

-- lemma eq_543 : sorry := sorry

/-! #### Inequalities -/

-- lemma eq_544 : sorry := sorry

/-! #### Condition Number -/

-- lemma eq_545 : sorry := sorry

/-! ### Rank -/

/-! #### Sylvester’s Inequality -/

lemma eq_546 (A : matrix m n ℝ) (B : matrix n r ℝ) :
  rank A + rank B - fintype.card n ≤ rank(A ⬝ B) ∧ rank(A ⬝ B) ≤ min (rank A) (rank B) :=
⟨sorry, rank_mul_le _ _⟩

/-! ### Integral Involving Dirac Delta Functions -/

-- lemma eq_547 : sorry := sorry
-- lemma eq_548 : sorry := sorry

/-! ### Miscellaneous -/

lemma eq_549 {𝕂} [is_R_or_C 𝕂] (A : matrix m n 𝕂) :
  A.rank = Aᵀ.rank ∧ A.rank = (A ⬝ Aᵀ).rank ∧ A.rank = (Aᵀ ⬝ A).rank :=
⟨eq.symm sorry, eq.symm sorry, eq.symm sorry⟩
lemma eq_550 (A : matrix m m ℝ) : A.pos_def ↔ ∃ B : (matrix m m ℝ)ˣ, A = B ⬝ Bᵀ :=
sorry

end matrix_cookbook
