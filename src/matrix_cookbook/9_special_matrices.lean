import data.complex.basic
import linear_algebra.matrix.hermitian
import linear_algebra.matrix.symmetric
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.adjugate
import linear_algebra.vandermonde

/-! # Special Matrices -/

variables {R : Type*} {l m n p q r : Type*}
variables [fintype l] [fintype m] [fintype n] [fintype p] [fintype q] [fintype r]
variables [decidable_eq l] [decidable_eq m] [decidable_eq n] [decidable_eq p] [decidable_eq q] [decidable_eq r]
variables [field R]

open matrix
open_locale matrix big_operators
open equiv equiv.perm finset

namespace matrix_cookbook

/-! ## Block matrices -/

/-! ### Multiplication -/

/-! ### The Determinant -/

lemma eq_397
  (A₁₁ : matrix m m R) (A₁₂ : matrix m n R) (A₂₁ : matrix n m R) (A₂₂ : matrix n n R)
  [invertible A₂₂] :
    (from_blocks A₁₁ A₁₂ A₂₁ A₂₂).det = A₂₂.det * (A₁₁ - A₁₂⬝⅟A₂₂⬝A₂₁).det :=
det_from_blocks₂₂ _ _ _ _
lemma eq_398 (A₁₁ : matrix m m R) (A₁₂ : matrix m n R) (A₂₁ : matrix n m R) (A₂₂ : matrix n n R)
  [invertible A₁₁] :
    (from_blocks A₁₁ A₁₂ A₂₁ A₂₂).det = A₁₁.det * (A₂₂ - A₂₁⬝⅟A₁₁⬝A₁₂).det :=
det_from_blocks₁₁ _ _ _ _

/-! ### The Inverse -/

-- lemma block_inv 
-- (A₁₁ : matrix m m R) (A₁₂ : matrix m n R) (A₂₁ : matrix n m R) (A₂₂ : matrix n n R)
--   [invertible A₂₂] [invertible (A₁₁ - A₁₂⬝⅟A₂₂⬝A₂₁)] : 
--   inver

/-- Eq 399 is the definition of `C₁`, this is the equation below it without `C₂` at all. -/
lemma eq_399 (A₁₁ : matrix m m R) (A₁₂ : matrix m n R) (A₂₁ : matrix n m R) (A₂₂ : matrix n n R)
  [invertible A₂₂] [invertible (A₁₁ - A₁₂⬝⅟A₂₂⬝A₂₁)] :
  (from_blocks A₁₁ A₁₂ A₂₁ A₂₂)⁻¹ =
    let 
    C₁ := A₁₁ - A₁₂⬝⅟A₂₂⬝A₂₁, i1 : invertible C₁ := ‹_› in by exactI
    -- let
    -- C₂ := A₂₂ - A₂₁⬝⅟A₁₁⬝A₁₂, i2 : invertible C₂ := ‹_› in by exactI
    from_blocks
      (⅟C₁)          (-⅟C₁⬝A₁₂⬝⅟A₂₂)
      (-⅟A₂₂⬝A₂₁⬝⅟C₁) (⅟A₂₂ + ⅟A₂₂⬝A₂₁⬝⅟C₁⬝A₁₂⬝⅟A₂₂) := 
begin
  have iA: (A₁₁ - A₁₂ ⬝ ⅟A₂₂ ⬝ A₂₁)⁻¹ = ⅟(A₁₁ - A₁₂ ⬝ ⅟A₂₂ ⬝ A₂₁), by simp only [inv_of_eq_nonsing_inv],
  have iA2: (A₁₁ - A₁₂ ⬝ A₂₂⁻¹ ⬝ A₂₁) = (A₁₁ - A₁₂ ⬝ ⅟A₂₂ ⬝ A₂₁), by rw [← inv_of_eq_nonsing_inv],
  have iA3: (A₁₂ ⬝ A₂₂⁻¹ ⬝ A₂₁ - A₁₁) = -(A₁₁ - A₁₂ ⬝ ⅟A₂₂ ⬝ A₂₁), by {
    simp only [inv_of_eq_nonsing_inv, neg_sub],
  },
  apply inv_eq_left_inv,
  rw from_blocks_multiply,
  repeat {rw inv_of_eq_nonsing_inv},
  simp only [matrix.neg_mul, inv_mul_cancel_right_of_invertible, add_right_neg],

  have a11 : ((A₁₁ - A₁₂ ⬝ A₂₂⁻¹ ⬝ A₂₁)⁻¹ ⬝ A₁₁ +
    -((A₁₁ - A₁₂ ⬝ A₂₂⁻¹ ⬝ A₂₁)⁻¹ ⬝ A₁₂ ⬝ A₂₂⁻¹ ⬝ A₂₁)) = 1, by {
    rw ← sub_eq_add_neg,
    rw matrix.mul_assoc (A₁₁ - A₁₂ ⬝ A₂₂⁻¹ ⬝ A₂₁)⁻¹ _,
    rw matrix.mul_assoc (A₁₁ - A₁₂ ⬝ A₂₂⁻¹ ⬝ A₂₁)⁻¹ _,
    rw ← matrix.mul_sub (A₁₁ - A₁₂ ⬝ A₂₂⁻¹ ⬝ A₂₁)⁻¹ _ _,
    rw [iA2, iA, matrix.inv_of_mul_self],
  },
  
  have a21 : (-(A₂₂⁻¹ ⬝ A₂₁ ⬝ (A₁₁ - A₁₂ ⬝ A₂₂⁻¹ ⬝ A₂₁)⁻¹ ⬝ A₁₁) +
     (A₂₂⁻¹ + A₂₂⁻¹ ⬝ A₂₁ ⬝ (A₁₁ - A₁₂ ⬝ A₂₂⁻¹ ⬝ A₂₁)⁻¹ ⬝ A₁₂ ⬝ A₂₂⁻¹) ⬝ A₂₁) = 0, by {
    rw matrix.add_mul,
    rw add_comm,
    rw ←  sub_eq_add_neg, 
    rw matrix.mul_assoc (A₂₂⁻¹⬝A₂₁⬝(A₁₁ - A₁₂ ⬝ A₂₂⁻¹ ⬝ A₂₁)⁻¹) _ _ ,
    rw matrix.mul_assoc (A₂₂⁻¹⬝A₂₁⬝(A₁₁ - A₁₂ ⬝ A₂₂⁻¹ ⬝ A₂₁)⁻¹) _ _ ,

    have hx : A₂₂⁻¹⬝A₂₁⬝(A₁₁ - A₁₂⬝A₂₂⁻¹⬝A₂₁)⁻¹⬝(A₁₂⬝A₂₂⁻¹⬝A₂₁) - A₂₂⁻¹⬝A₂₁⬝(A₁₁ - A₁₂⬝A₂₂⁻¹⬝A₂₁)⁻¹⬝A₁₁ 
    = -A₂₂⁻¹⬝A₂₁, by {
      rw ← matrix.mul_sub (A₂₂⁻¹⬝A₂₁⬝(A₁₁ - A₁₂ ⬝ A₂₂⁻¹ ⬝ A₂₁)⁻¹),
      rw iA3, rw iA2, rw iA, 
      rw matrix.mul_neg, rw matrix.mul_inv_of_mul_self_cancel, rw matrix.neg_mul,
    },
    rw ← add_sub, rw hx, 
    simp only [matrix.neg_mul, add_right_neg],

    -- something seems extremely stupid here. rw hx does not wokr!
    -- rw rw ← matrix.mul_sub (A₂₂⁻¹⬝A₂₁⬝(A₁₁ - A₁₂ ⬝ A₂₂⁻¹ ⬝ A₂₁)⁻¹), that works inside the have hx does not work outside. I ran out of steam to massage this stupid thing.
    -- Ahhhh: the addition statement followed by subtraction had the imaginary brackets around the first pair preventing the matching of hx. We use rw ← add_sub to place the brackets around the subtraction
  },
  have a22 : (-(A₂₂⁻¹ ⬝ A₂₁ ⬝ (A₁₁ - A₁₂ ⬝ A₂₂⁻¹ ⬝ A₂₁)⁻¹ ⬝ A₁₂) +
     (A₂₂⁻¹ + A₂₂⁻¹ ⬝ A₂₁ ⬝ (A₁₁ - A₁₂ ⬝ A₂₂⁻¹ ⬝ A₂₁)⁻¹ ⬝ A₁₂ ⬝ A₂₂⁻¹) ⬝ A₂₂) = 1, by {
    rw matrix.add_mul,
    rw [inv_mul_of_invertible, inv_mul_cancel_right_of_invertible, neg_add_cancel_comm_assoc],
  },

  rw [a11, a21, a22], 
  rw from_blocks_one,
end

/-- Eq 400 is the definition of `C₂`,  this is the equation below it without `C₁` at all. -/
lemma eq_400 (A₁₁ : matrix m m R) (A₁₂ : matrix m n R) (A₂₁ : matrix n m R) (A₂₂ : matrix n n R)
  [invertible A₁₁] [invertible (A₂₂ - A₂₁⬝⅟A₁₁⬝A₁₂)] :
  (from_blocks A₁₁ A₁₂ A₂₁ A₂₂)⁻¹ =
    let C₂ := A₂₂ - A₂₁⬝⅟A₁₁⬝A₁₂, i : invertible C₂ := ‹_› in by exactI
    from_blocks
      (⅟A₁₁ + ⅟A₁₁⬝A₁₂⬝⅟C₂⬝A₂₁⬝⅟A₁₁) (-⅟A₁₁⬝A₁₂⬝⅟C₂)
      (-⅟C₂⬝A₂₁⬝⅟A₁₁)                (⅟C₂) := 
begin
  dsimp only,
  set C₂ := A₂₂ - A₂₁⬝⅟A₁₁⬝A₁₂,

  show _ = from_blocks
      (⅟A₁₁ + ⅟A₁₁⬝A₁₂⬝⅟C₂⬝A₂₁⬝⅟A₁₁) (-⅟A₁₁⬝A₁₂⬝⅟C₂)
      (-⅟C₂⬝A₂₁⬝⅟A₁₁)                (⅟C₂),
  apply inv_eq_left_inv,
  
  rw [from_blocks_multiply, ←from_blocks_one],
  congr,
  { -- A11 Block
  rw matrix.add_mul, rw matrix.inv_of_mul_self, 
  simp only [inv_of_eq_nonsing_inv, inv_mul_cancel_right_of_invertible, matrix.neg_mul, add_neg_cancel_right],
  },
  { -- A12 Block
    rw [matrix.add_mul, add_assoc], 
    repeat {rw matrix.neg_mul}, 
    rw [←sub_eq_add_neg, matrix.mul_assoc _ _ (⅟C₂), matrix.mul_assoc (⅟A₁₁⬝(A₁₂⬝⅟C₂)), 
      matrix.mul_assoc, ←matrix.mul_sub (⅟A₁₁⬝(A₁₂⬝⅟C₂)), matrix.mul_assoc, 
      ← neg_sub, matrix.mul_neg, matrix.mul_inv_of_mul_self_cancel],
    rw [matrix.mul_neg, add_right_neg],
  },
  { -- A21 Block
    rw [matrix.mul_assoc, matrix.inv_of_mul_self, matrix.mul_one, matrix.neg_mul, neg_add_self],
  },
  { -- A22 Block
    rw [matrix.mul_assoc, matrix.mul_assoc, matrix.neg_mul, ← matrix.mul_neg,
    ← matrix.mul_add, neg_add_eq_sub, ← matrix.mul_assoc, matrix.inv_of_mul_self],
  }
end

/-! ### Block diagonal -/

lemma eq_401 (A₁₁ : matrix m m R) (A₂₂ : matrix n n R) :
  (from_blocks A₁₁ 0 0 A₂₂)⁻¹ = from_blocks A₁₁⁻¹ 0 0 A₂₂⁻¹ := sorry
lemma eq_402 (A₁₁ : matrix m m R) (A₂₂ : matrix n n R) :
  det (from_blocks A₁₁ 0 0 A₂₂) = det A₁₁ * det A₂₂ := det_from_blocks_zero₁₂ _ _ _

/-! ### Schur complement -/

/-! ## Discrete Fourier Transform Matrix, The -/

lemma eq_403 : sorry := sorry
lemma eq_404 : sorry := sorry
lemma eq_405 : sorry := sorry
lemma eq_406 : sorry := sorry
lemma eq_407 : sorry := sorry
lemma eq_408 : sorry := sorry
lemma eq_409 : sorry := sorry
lemma eq_410 : sorry := sorry
lemma eq_411 : sorry := sorry
lemma eq_412 : sorry := sorry

/-! ## Hermitian Matrices and skew-Hermitian -/

lemma eq_413 (A : matrix m m ℂ) :
  A.is_hermitian ↔ ∀ x : m → ℂ, is_self_adjoint (star x ⬝ᵥ A.mul_vec x) := sorry
lemma eq_414 (A : matrix m m ℂ) : 
  A.is_hermitian ↔ sorry := sorry

/-! ### Skew-Hermitian -/

lemma eq_415 (A : matrix m m ℂ) : A.is_hermitian ↔ complex.I • A ∈ skew_adjoint (matrix m m ℂ) := sorry
lemma eq_416 (A : matrix m m ℂ) :
  A ∈ skew_adjoint (matrix m m ℂ) ↔ ∀x y, star x ⬝ᵥ A.mul_vec y = - star x ⬝ᵥ Aᴴ.mul_vec y := sorry
lemma eq_417 (A : matrix m m ℂ) :
  A.is_hermitian → sorry := sorry

/-! ## Idempotent Matrices -/

section
variables (A : matrix m m R) (B : matrix m m R) 

lemma eq_418 (hA : is_idempotent_elem A) (n : ℕ) (hn : n ≠ 0) :
  A^n = A := by { cases n, { cases hn rfl }, exact hA.pow_succ_eq n }
lemma eq_419 (hA : is_idempotent_elem A) : is_idempotent_elem (1 - A) :=
hA.one_sub
lemma eq_420 [star_ring R] (hA : is_idempotent_elem A) : is_idempotent_elem Aᴴ :=
sorry
lemma eq_421 [star_ring R] (hA : is_idempotent_elem A) :
  is_idempotent_elem (1 - Aᴴ) := sorry
lemma eq_422 (hA : is_idempotent_elem A) (hB : is_idempotent_elem B) (h : commute A B) :
  is_idempotent_elem (A⬝B) :=
hA.mul_of_commute h hB
lemma eq_423 (hA : is_idempotent_elem A) : sorry = trace A := sorry
lemma eq_424 (hA : is_idempotent_elem A) : A⬝(1-A) = 0 :=
by simp [mul_sub, ←matrix.mul_eq_mul, hA.eq]
lemma eq_425  (hA : is_idempotent_elem A) : (1-A)⬝A = 0 :=
by simp [sub_mul, ←matrix.mul_eq_mul, hA.eq]
lemma eq_426 : sorry := sorry
lemma eq_427 : sorry := sorry

end

/-! ### Nilpotent -/

-- lemma eq_428 : sorry := sorry

-- /-! ### Unipotent -/

-- lemma eq_429 : sorry := sorry

-- /-! ## Orthogonal matrices -/

-- /-! ### Ortho-Sym -/

-- lemma eq_430 : sorry := sorry
-- lemma eq_431 : sorry := sorry
-- lemma eq_432 : sorry := sorry
-- lemma eq_433 : sorry := sorry

-- /-! ### Ortho-Skew -/

-- lemma eq_434 : sorry := sorry
-- lemma eq_435 : sorry := sorry
-- lemma eq_436 : sorry := sorry
-- lemma eq_437 : sorry := sorry

-- /-! ### Decomposition -/

-- lemma eq_438 : sorry := sorry

-- /-! ## Positive Definite and Semi-definite Matrices -/

-- /-! ### Definitions -/

-- lemma eq_439 : sorry := sorry
-- lemma eq_440 : sorry := sorry

-- /-! ### Eigenvalues -/

-- lemma eq_441 : sorry := sorry

-- /-! ### Trace -/

-- lemma eq_442 : sorry := sorry

/-! ### Inverse -/

/-! ### Diagonal -/

/-! ### Decomposition I -/

/-! ### Decomposition II -/

/-! ### Equation with zeros -/

/-! ### Rank of product -/

/-! ### Positive definite property -/

/-! ### Outer Product -/

/-! ### Small pertubations -/

/-! ### Hadamard inequality -/

/-! ### Hadamard product relation -/

/-! ## Singleentry Matrix, The -/

/-! ### Definition -/

-- lemma eq_443 : sorry := sorry

-- /-! ### Swap and Zeros -/

-- lemma eq_444 : sorry := sorry
-- lemma eq_445 : sorry := sorry

-- /-! ### Rewriting product of elements -/

-- lemma eq_446 : sorry := sorry
-- lemma eq_447 : sorry := sorry
-- lemma eq_448 : sorry := sorry
-- lemma eq_449 : sorry := sorry

-- /-! ### Properties of the Singleentry Matrix -/

-- /-! ### The Singleentry Matrix in Scalar Expressions -/

-- lemma eq_450 : sorry := sorry
-- lemma eq_451 : sorry := sorry
-- lemma eq_452 : sorry := sorry
-- lemma eq_453 : sorry := sorry
-- lemma eq_454 : sorry := sorry
-- lemma eq_455 : sorry := sorry

-- /-! ### Structure Matrices -/

-- lemma eq_456 : sorry := sorry
-- lemma eq_457 : sorry := sorry
-- lemma eq_458 : sorry := sorry

-- /-! ## Symmetric, Skew-symmetric/Antisymmetric -/

-- /-! ### Symmetric -/

lemma eq_459 (A : matrix m m R) : A.is_symm ↔ A = Aᵀ := eq_comm

-- /-! ### Skew-symmetric/Antisymmetric -/

lemma eq_460 (A : matrix m m R) : sorry ↔ A = -Aᵀ := sorry
lemma eq_461 (A : matrix m m R) (hA : A = -Aᵀ) : det Aᵀ = (-1)^fintype.card m * det A :=
by rw [hA, transpose_neg, transpose_transpose, det_neg, ←hA]
lemma eq_462 (A : matrix m m R) (hA : A = -Aᵀ) (hn : odd (fintype.card m)) : 
  -det A = 0 ∧ det (-A) = 0 := ⟨sorry, sorry⟩

-- /-! ### Decomposition -/

-- lemma eq_463 : sorry := sorry
-- lemma eq_464 : sorry := sorry

-- /-! ## Toeplitz Matrices -/

-- lemma eq_465 : sorry := sorry
-- lemma eq_466 : sorry := sorry
-- lemma eq_467 : sorry := sorry
-- lemma eq_468 : sorry := sorry
-- lemma eq_469 : sorry := sorry

-- /-! ### Properties of Toeplitz Matrices -/

-- /-! ## Transition matrices -/

-- lemma eq_470 : sorry := sorry
-- lemma eq_471 : sorry := sorry
-- lemma eq_472 : sorry := sorry
-- lemma eq_473 : sorry := sorry
-- lemma eq_474 : sorry := sorry

/-! ## Units, Permutation and Shift -/

/-! ### Unit vector -/

/-! ### Rows and Columns -/

lemma eq_475 (A : matrix m n R) (i) : A i = A.vec_mul (pi.single i 1) :=
funext $ λ _, (vec_mul_std_basis _ _ _).symm
lemma eq_476 (A : matrix m n R) (j) : (λ i, A i j) = A.mul_vec (pi.single j 1) :=
funext $ λ _, (mul_vec_std_basis _ _ _).symm

/-! ### Permutations -/

lemma eq_477 :
  (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : matrix _ _ R)
    = of ![(pi.single 1 1 : fin 3 → R), pi.single 0 1, pi.single 2 1] :=
by { ext i j, fin_cases i; fin_cases j; refl }
lemma eq_478 (e : equiv.perm m) :
  e.to_pequiv.to_matrix ⬝ e.to_pequiv.to_matrixᵀ = (1 : matrix m m R) :=
by rw [←pequiv.to_matrix_symm, ←pequiv.to_matrix_trans,
  ←equiv.to_pequiv_symm, ←equiv.to_pequiv_trans, equiv.self_trans_symm,
  equiv.to_pequiv_refl, pequiv.to_matrix_refl]
lemma eq_479 : sorry := sorry

/-! ### Translation, Shift or Lag Operators -/

-- lemma eq_480 : sorry := sorry
-- lemma eq_481 : sorry := sorry
-- lemma eq_482 : sorry := sorry
-- lemma eq_483 : sorry := sorry
-- lemma eq_484 : sorry := sorry

-- /-! ## Vandermonde Matrices -/

lemma eq_485 {n : ℕ} (v : fin n → R) (i j : fin n) : vandermonde v i j = v i ^ (j : ℕ) := vandermonde_apply _ _ _
lemma eq_486 {n : ℕ} (v : fin n → R) :det (vandermonde v) = ∏ i : fin n, ∏ j in finset.Ioi i, (v j - v i) := det_vandermonde _

end matrix_cookbook