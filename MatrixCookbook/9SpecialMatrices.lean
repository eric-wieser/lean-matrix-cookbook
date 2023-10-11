import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Vandermonde

/-! # Special Matrices -/


variable {R : Type _} {l m n p q r : Type _}

variable [Fintype l] [Fintype m] [Fintype n] [Fintype p] [Fintype q] [Fintype r]

variable [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
  [DecidableEq r]

variable [Field R]

open Matrix

open scoped BigOperators

open scoped Matrix

namespace MatrixCookbook

/-! ## Block matrices -/


/-! ### Multiplication -/


/-! ### The Determinant -/


theorem eq_397 (A₁₁ : Matrix m m R) (A₁₂ : Matrix m n R) (A₂₁ : Matrix n m R) (A₂₂ : Matrix n n R)
    [Invertible A₂₂] : (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).det = A₂₂.det * (A₁₁ - A₁₂ ⬝ ⅟ A₂₂ ⬝ A₂₁).det :=
  det_fromBlocks₂₂ _ _ _ _

theorem eq_398 (A₁₁ : Matrix m m R) (A₁₂ : Matrix m n R) (A₂₁ : Matrix n m R) (A₂₂ : Matrix n n R)
    [Invertible A₁₁] : (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).det = A₁₁.det * (A₂₂ - A₂₁ ⬝ ⅟ A₁₁ ⬝ A₁₂).det :=
  det_fromBlocks₁₁ _ _ _ _

/-! ### The Inverse -/


/-- Eq 399 is the definition of `C₁`, this is the equation below it without `C₂` at all. -/
theorem eq_399 (A₁₁ : Matrix m m R) (A₁₂ : Matrix m n R) (A₂₁ : Matrix n m R) (A₂₂ : Matrix n n R)
    [Invertible A₂₂] [Invertible (A₁₁ - A₁₂ ⬝ ⅟ A₂₂ ⬝ A₂₁)] :
    (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)⁻¹ =
      let C₁ := A₁₁ - A₁₂ ⬝ ⅟ A₂₂ ⬝ A₂₁
      let i : Invertible C₁ := ‹_›
      from_blocks (⅟ C₁) (-⅟ C₁ ⬝ A₁₂ ⬝ ⅟ A₂₂) (-⅟ A₂₂ ⬝ A₂₁ ⬝ ⅟ C₁)
        (⅟ A₂₂ + ⅟ A₂₂ ⬝ A₂₁ ⬝ ⅟ C₁ ⬝ A₁₂ ⬝ ⅟ A₂₂) :=
  by
  letI := from_blocks₂₂_invertible A₁₁ A₁₂ A₂₁ A₂₂
  convert inv_of_from_blocks₂₂_eq A₁₁ A₁₂ A₂₁ A₂₂
  rw [inv_of_eq_nonsing_inv]

/-- Eq 400 is the definition of `C₂`,  this is the equation below it without `C₁` at all. -/
theorem eq_400 (A₁₁ : Matrix m m R) (A₁₂ : Matrix m n R) (A₂₁ : Matrix n m R) (A₂₂ : Matrix n n R)
    [Invertible A₁₁] [Invertible (A₂₂ - A₂₁ ⬝ ⅟ A₁₁ ⬝ A₁₂)] :
    (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)⁻¹ =
      let C₂ := A₂₂ - A₂₁ ⬝ ⅟ A₁₁ ⬝ A₁₂
      let i : Invertible C₂ := ‹_›
      from_blocks (⅟ A₁₁ + ⅟ A₁₁ ⬝ A₁₂ ⬝ ⅟ C₂ ⬝ A₂₁ ⬝ ⅟ A₁₁) (-⅟ A₁₁ ⬝ A₁₂ ⬝ ⅟ C₂)
        (-⅟ C₂ ⬝ A₂₁ ⬝ ⅟ A₁₁) (⅟ C₂) :=
  by
  letI := from_blocks₁₁_invertible A₁₁ A₁₂ A₂₁ A₂₂
  convert inv_of_from_blocks₁₁_eq A₁₁ A₁₂ A₂₁ A₂₂
  rw [inv_of_eq_nonsing_inv]

/-! ### Block diagonal -/


theorem eq_401 (A₁₁ : Matrix m m R) (A₂₂ : Matrix n n R) (h : IsUnit A₁₁ ↔ IsUnit A₂₂) :
    (fromBlocks A₁₁ 0 0 A₂₂)⁻¹ = fromBlocks A₁₁⁻¹ 0 0 A₂₂⁻¹ :=
  (inv_fromBlocks_zero₁₂_of_isUnit_iff _ _ _ h).trans <| by simp

theorem eq_402 (A₁₁ : Matrix m m R) (A₂₂ : Matrix n n R) :
    det (fromBlocks A₁₁ 0 0 A₂₂) = det A₁₁ * det A₂₂ :=
  det_fromBlocks_zero₁₂ _ _ _

/-! ### Schur complement -/


/-! ## Discrete Fourier Transform Matrix, The -/


theorem eq403 : sorry :=
  sorry

theorem eq404 : sorry :=
  sorry

theorem eq405 : sorry :=
  sorry

theorem eq406 : sorry :=
  sorry

theorem eq407 : sorry :=
  sorry

theorem eq408 : sorry :=
  sorry

theorem eq409 : sorry :=
  sorry

theorem eq410 : sorry :=
  sorry

theorem eq411 : sorry :=
  sorry

theorem eq412 : sorry :=
  sorry

/-! ## Hermitian Matrices and skew-Hermitian -/


theorem eq_413 (A : Matrix m m ℂ) :
    A.IsHermitian ↔ ∀ x : m → ℂ, IsSelfAdjoint (star x ⬝ᵥ A.mulVec x) :=
  sorry

theorem eq_414 (A : Matrix m m ℂ) : A.IsHermitian ↔ sorry :=
  sorry

/-! ### Skew-Hermitian -/


theorem eq_415 (A : Matrix m m ℂ) : A.IsHermitian ↔ Complex.I • A ∈ skewAdjoint (Matrix m m ℂ) :=
  sorry

theorem eq_416 (A : Matrix m m ℂ) :
    A ∈ skewAdjoint (Matrix m m ℂ) ↔ ∀ x y, star x ⬝ᵥ A.mulVec y = -star x ⬝ᵥ Aᴴ.mulVec y :=
  sorry

theorem eq417 (A : Matrix m m ℂ) : A.IsHermitian → sorry :=
  sorry

/-! ## Idempotent Matrices -/


section

variable (A : Matrix m m R) (B : Matrix m m R)

theorem eq_418 (hA : IsIdempotentElem A) (n : ℕ) (hn : n ≠ 0) : A ^ n = A := by cases n;
  · cases hn rfl; exact hA.pow_succ_eq n

theorem eq_419 (hA : IsIdempotentElem A) : IsIdempotentElem (1 - A) :=
  hA.one_sub

theorem eq_420 [StarRing R] (hA : IsIdempotentElem A) : IsIdempotentElem Aᴴ :=
  sorry

theorem eq_421 [StarRing R] (hA : IsIdempotentElem A) : IsIdempotentElem (1 - Aᴴ) :=
  sorry

theorem eq_422 (hA : IsIdempotentElem A) (hB : IsIdempotentElem B) (h : Commute A B) :
    IsIdempotentElem (A ⬝ B) :=
  hA.mul_of_commute h hB

theorem eq_423 (hA : IsIdempotentElem A) : sorry = trace A :=
  sorry

theorem eq_424 (hA : IsIdempotentElem A) : A ⬝ (1 - A) = 0 := by
  simp [mul_sub, ← Matrix.mul_eq_mul, hA.eq]

theorem eq_425 (hA : IsIdempotentElem A) : (1 - A) ⬝ A = 0 := by
  simp [sub_mul, ← Matrix.mul_eq_mul, hA.eq]

theorem eq426 : sorry :=
  sorry

theorem eq427 : sorry :=
  sorry

end

/-! ### Nilpotent -/


theorem eq428 : sorry :=
  sorry

/-! ### Unipotent -/


theorem eq429 : sorry :=
  sorry

/-! ## Orthogonal matrices -/


/-! ### Ortho-Sym -/


theorem eq430 : sorry :=
  sorry

theorem eq431 : sorry :=
  sorry

theorem eq432 : sorry :=
  sorry

theorem eq433 : sorry :=
  sorry

/-! ### Ortho-Skew -/


theorem eq434 : sorry :=
  sorry

theorem eq435 : sorry :=
  sorry

theorem eq436 : sorry :=
  sorry

theorem eq437 : sorry :=
  sorry

/-! ### Decomposition -/


theorem eq438 : sorry :=
  sorry

/-! ## Positive Definite and Semi-definite Matrices -/


/-! ### Definitions -/


theorem eq439 : sorry :=
  sorry

theorem eq440 : sorry :=
  sorry

/-! ### Eigenvalues -/


theorem eq441 : sorry :=
  sorry

/-! ### Trace -/


theorem eq442 : sorry :=
  sorry

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


theorem eq443 : sorry :=
  sorry

/-! ### Swap and Zeros -/


theorem eq444 : sorry :=
  sorry

theorem eq445 : sorry :=
  sorry

/-! ### Rewriting product of elements -/


theorem eq446 : sorry :=
  sorry

theorem eq447 : sorry :=
  sorry

theorem eq448 : sorry :=
  sorry

theorem eq449 : sorry :=
  sorry

/-! ### Properties of the Singleentry Matrix -/


/-! ### The Singleentry Matrix in Scalar Expressions -/


theorem eq450 : sorry :=
  sorry

theorem eq451 : sorry :=
  sorry

theorem eq452 : sorry :=
  sorry

theorem eq453 : sorry :=
  sorry

theorem eq454 : sorry :=
  sorry

theorem eq455 : sorry :=
  sorry

/-! ### Structure Matrices -/


theorem eq456 : sorry :=
  sorry

theorem eq457 : sorry :=
  sorry

theorem eq458 : sorry :=
  sorry

/-! ## Symmetric, Skew-symmetric/Antisymmetric -/


/-! ### Symmetric -/


theorem eq_459 (A : Matrix m m R) : A.IsSymm ↔ A = Aᵀ :=
  eq_comm

/-! ### Skew-symmetric/Antisymmetric -/


theorem eq_460 (A : Matrix m m R) : sorry ↔ A = -Aᵀ :=
  sorry

theorem eq_461 (A : Matrix m m R) (hA : A = -Aᵀ) : det Aᵀ = (-1) ^ Fintype.card m * det A := by
  rw [hA, transpose_neg, transpose_transpose, det_neg, ← hA]

theorem eq_462 (A : Matrix m m R) (hA : A = -Aᵀ) (hn : Odd (Fintype.card m)) :
    -det A = 0 ∧ det (-A) = 0 :=
  ⟨sorry, sorry⟩

/-! ### Decomposition -/


theorem eq463 : sorry :=
  sorry

theorem eq464 : sorry :=
  sorry

/-! ## Toeplitz Matrices -/


theorem eq465 : sorry :=
  sorry

theorem eq466 : sorry :=
  sorry

theorem eq467 : sorry :=
  sorry

theorem eq468 : sorry :=
  sorry

theorem eq469 : sorry :=
  sorry

/-! ### Properties of Toeplitz Matrices -/


/-! ## Transition matrices -/


theorem eq470 : sorry :=
  sorry

theorem eq471 : sorry :=
  sorry

theorem eq472 : sorry :=
  sorry

theorem eq473 : sorry :=
  sorry

theorem eq474 : sorry :=
  sorry

/-! ## Units, Permutation and Shift -/


/-! ### Unit vector -/


/-! ### Rows and Columns -/


theorem eq_475 (A : Matrix m n R) (i) : A i = A.vecMul (Pi.single i 1) :=
  funext fun _ => (vecMul_stdBasis _ _ _).symm

theorem eq_476 (A : Matrix m n R) (j) : (fun i => A i j) = A.mulVec (Pi.single j 1) :=
  funext fun _ => (mulVec_stdBasis _ _ _).symm

/-! ### Permutations -/


theorem eq_477 :
    (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix _ _ R) =
      of ![(Pi.single 1 1 : Fin 3 → R), Pi.single 0 1, Pi.single 2 1] :=
  by ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem eq_478 (e : Equiv.Perm m) :
    e.toPEquiv.toMatrix ⬝ e.toPEquiv.toMatrixᵀ = (1 : Matrix m m R) := by
  rw [← PEquiv.toMatrix_symm, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_symm, ←
    Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

theorem eq479 : sorry :=
  sorry

/-! ### Translation, Shift or Lag Operators -/


theorem eq480 : sorry :=
  sorry

theorem eq481 : sorry :=
  sorry

theorem eq482 : sorry :=
  sorry

theorem eq483 : sorry :=
  sorry

theorem eq484 : sorry :=
  sorry

/-! ## Vandermonde Matrices -/


theorem eq_485 {n : ℕ} (v : Fin n → R) (i j : Fin n) : vandermonde v i j = v i ^ (j : ℕ) :=
  vandermonde_apply _ _ _

theorem eq_486 {n : ℕ} (v : Fin n → R) :
    det (vandermonde v) = ∏ i : Fin n, ∏ j in Finset.Ioi i, (v j - v i) :=
  det_vandermonde _

end MatrixCookbook

