import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.trace
import data.real.nnreal
import topology.metric_space.basic
import data.matrix.notation
import ring_theory.power_series.basic
import analysis.normed_space.matrix_exponential
import data.matrix.kronecker
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

-- lemma eq_507 : sorry := sorry

/-- Note we have to "cast" between the types -/
lemma eq_508 (A : matrix m n R) (B : matrix r q R) (C : matrix l p R) :
  A ⊗ₖ (B ⊗ₖ C) = reindex (equiv.prod_assoc _ _ _) (equiv.prod_assoc _ _ _)
    ((A ⊗ₖ B) ⊗ₖ C) :=
(kronecker_assoc _ _ _).symm

lemma eq_509 (a b : R) (A : matrix m n R) (B : matrix r q R) :
  (a • A) ⊗ₖ (b • B) = (a*b) • (A ⊗ₖ B) :=
by rw [smul_kronecker, kronecker_smul, smul_smul]

lemma eq_510 (a b : R) (A : matrix m n R) (B : matrix r q R) :
  (A ⊗ₖ B)ᵀ = (Aᵀ ⊗ₖ Bᵀ) :=
by rw [kronecker_map_transpose]

lemma eq_511 (a b : R) (A : matrix l m R) (B : matrix p q R) (C : matrix m n R) (D : matrix q r R) :
  (A ⊗ₖ B) ⬝ (C ⊗ₖ D) = (A ⬝ C) ⊗ₖ (B ⬝ D) :=
by rw matrix.mul_kronecker_mul

lemma eq_512 (a b : R) (A : matrix m m R) (B : matrix n n R) :
  (A ⊗ₖ B)⁻¹ = (A⁻¹ ⊗ₖ B⁻¹) :=
sorry

-- lemma eq_513 : sorry := sorry
-- lemma eq_514 : sorry := sorry

lemma eq_515 (A : matrix m m R) (B : matrix n n R) :
  trace (A ⊗ₖ B) = trace A * trace B :=
by simp_rw [matrix.trace, matrix.diag, finset.sum_mul, finset.mul_sum,
    ←finset.univ_product_univ, finset.sum_product, kronecker_apply]

lemma eq_516 (A : matrix m m R) (B : matrix n n R) :
  det (A ⊗ₖ B) = det A ^ fintype.card m * det B ^ fintype.card n :=
sorry

-- lemma eq_516 : sorry := sorry
-- lemma eq_517 : sorry := sorry
-- lemma eq_518 : sorry := sorry
-- lemma eq_519 : sorry := sorry

/-! #### The Vec Operator -/

def vec (A : matrix m n R) : matrix (m × n) unit R :=
col (λ ij, A ij.1 ij.2)

-- lemma eq_520: sorry := sorry
lemma eq_521 (A B : matrix m n R) : (Aᵀ ⬝ B).trace = ((vec A)ᵀ ⬝ vec B) () () :=
sorry
lemma eq_522 (A B : matrix m n R) : vec (A + B) = vec A + vec B := rfl
lemma eq_523 (r : R) (A : matrix m n R) : vec (r • A) = r • vec A := rfl

-- lemma eq_524 : sorry := sorry

/-! ### Vector Norms -/

/-! #### Examples -/

lemma eq_525 (x : n → ℂ) : ‖(pi_Lp.equiv 1 _).symm x‖ = ∑ i, complex.abs (x i) :=
by simpa using pi_Lp.norm_eq_of_nat 1 (nat.cast_one.symm) ((pi_Lp.equiv 1 _).symm x)

lemma eq_526 (x : n → ℂ) : ↑(‖(pi_Lp.equiv 2 _).symm x‖^2) = star x ⬝ᵥ x := sorry

lemma eq_527 (x : n → ℂ) (p : ℝ≥0∞) (h : 0 < p.to_real) :
  ‖(pi_Lp.equiv p _).symm x‖ = (∑ i, complex.abs (x i) ^ p.to_real)^(1/p.to_real) :=
by simp_rw [pi_Lp.norm_eq_sum h, pi_Lp.equiv_symm_apply, complex.norm_eq_abs]

lemma eq_528 (x : n → ℂ) :
  ‖(pi_Lp.equiv ∞ _).symm x‖ = ⨆ i, complex.abs (x i) :=
by simp_rw [pi_Lp.norm_eq_csupr, pi_Lp.equiv_symm_apply, complex.norm_eq_abs]

/-! ### Matrix Norms -/

/-! #### Definitions -/

-- lemma eq_529 : sorry := sorry
-- lemma eq_530 : sorry := sorry
-- lemma eq_531 : sorry := sorry
-- lemma eq_532 : sorry := sorry

/-! #### Induced Norm or Operator Norm -/

-- lemma eq_533 : sorry := sorry
-- lemma eq_534 : sorry := sorry
-- lemma eq_535 : sorry := sorry
-- lemma eq_536 : sorry := sorry

/-! #### Examples -/

-- lemma eq_537 : sorry := sorry
-- lemma eq_538 : sorry := sorry
-- lemma eq_539 : sorry := sorry
-- lemma eq_540 : sorry := sorry
-- lemma eq_541 : sorry := sorry
-- lemma eq_542 : sorry := sorry
-- lemma eq_543 : sorry := sorry

/-! #### Inequalities -/

-- lemma eq_544 : sorry := sorry

/-! #### Condition Number -/

-- lemma eq_545 : sorry := sorry

/-! ### Rank -/

/-! #### Sylvester’s Inequality -/

-- lemma eq_546 : sorry := sorry

/-! ### Integral Involving Dirac Delta Functions -/

-- lemma eq_547 : sorry := sorry
-- lemma eq_548 : sorry := sorry

/-! ### Miscellaneous -/

-- lemma eq_549 : sorry := sorry
-- lemma eq_550 : sorry := sorry

end matrix_cookbook
