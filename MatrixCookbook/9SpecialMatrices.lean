import Mathlib.Algebra.Ring.Idempotents
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.PEquiv
import Mathlib.Data.Matrix.Reflection
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.Circulant

/-! # Special Matrices -/


variable {R : Type _} {l m n p q r : Type _}

variable [Fintype l] [Fintype m] [Fintype n] [Fintype p] [Fintype q] [Fintype r]

variable [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
  [DecidableEq r]

variable [Field R]

open Matrix

open scoped BigOperators

open scoped Matrix

open Real Complex

namespace MatrixCookbook

/-! ## Block matrices -/


/-! ### Multiplication -/


/-! ### The Determinant -/


theorem eq_397 (A₁₁ : Matrix m m R) (A₁₂ : Matrix m n R) (A₂₁ : Matrix n m R) (A₂₂ : Matrix n n R)
    [Invertible A₂₂] : (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).det = A₂₂.det * (A₁₁ - A₁₂ * ⅟ A₂₂ * A₂₁).det :=
  det_fromBlocks₂₂ _ _ _ _

theorem eq_398 (A₁₁ : Matrix m m R) (A₁₂ : Matrix m n R) (A₂₁ : Matrix n m R) (A₂₂ : Matrix n n R)
    [Invertible A₁₁] : (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).det = A₁₁.det * (A₂₂ - A₂₁ * ⅟ A₁₁ * A₁₂).det :=
  det_fromBlocks₁₁ _ _ _ _

/-! ### The Inverse -/


/-- Eq 399 is the definition of `C₁`, this is the equation below it without `C₂` at all. -/
theorem eq_399 (A₁₁ : Matrix m m R) (A₁₂ : Matrix m n R) (A₂₁ : Matrix n m R) (A₂₂ : Matrix n n R)
    [Invertible A₂₂] [Invertible (A₁₁ - A₁₂ * ⅟ A₂₂ * A₂₁)] :
    (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)⁻¹ =
      let C₁ := A₁₁ - A₁₂ * ⅟ A₂₂ * A₂₁
      let i : Invertible C₁ := ‹_›
      fromBlocks
        (⅟ C₁) (-(⅟ C₁ * A₁₂ * ⅟ A₂₂))
        (-(⅟ A₂₂ * A₂₁ * ⅟ C₁)) (⅟ A₂₂ + ⅟ A₂₂ * A₂₁ * ⅟ C₁ * A₁₂ * ⅟ A₂₂) := by
  letI := fromBlocks₂₂Invertible A₁₁ A₁₂ A₂₁ A₂₂
  convert invOf_fromBlocks₂₂_eq A₁₁ A₁₂ A₂₁ A₂₂
  rw [invOf_eq_nonsing_inv]

/-- Eq 400 is the definition of `C₂`,  this is the equation below it without `C₁` at all. -/
theorem eq_400 (A₁₁ : Matrix m m R) (A₁₂ : Matrix m n R) (A₂₁ : Matrix n m R) (A₂₂ : Matrix n n R)
    [Invertible A₁₁] [Invertible (A₂₂ - A₂₁ * ⅟ A₁₁ * A₁₂)] :
    (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)⁻¹ =
      let C₂ := A₂₂ - A₂₁ * ⅟ A₁₁ * A₁₂
      let i : Invertible C₂ := ‹_›
      fromBlocks
        (⅟ A₁₁ + ⅟ A₁₁ * A₁₂ * ⅟ C₂ * A₂₁ * ⅟ A₁₁) (-(⅟ A₁₁ * A₁₂ * ⅟ C₂))
        (-(⅟ C₂ * A₂₁ * ⅟ A₁₁)) (⅟ C₂) := by
  letI := fromBlocks₁₁Invertible A₁₁ A₁₂ A₂₁ A₂₂
  convert invOf_fromBlocks₁₁_eq A₁₁ A₁₂ A₂₁ A₂₂
  rw [invOf_eq_nonsing_inv]

/-! ### Block diagonal -/


theorem eq_401 (A₁₁ : Matrix m m R) (A₂₂ : Matrix n n R) (h : IsUnit A₁₁ ↔ IsUnit A₂₂) :
    (fromBlocks A₁₁ 0 0 A₂₂)⁻¹ = fromBlocks A₁₁⁻¹ 0 0 A₂₂⁻¹ :=
  (inv_fromBlocks_zero₁₂_of_isUnit_iff _ _ _ h).trans <| by simp

theorem eq_402 (A₁₁ : Matrix m m R) (A₂₂ : Matrix n n R) :
    det (fromBlocks A₁₁ 0 0 A₂₂) = det A₁₁ * det A₂₂ :=
  det_fromBlocks_zero₁₂ _ _ _

/-! ### Schur complement -/


/-! ## Discrete Fourier Transform Matrix, The -/
noncomputable def Wₙ {N: ℕ}: Matrix (Fin N) (Fin N) ℂ :=
  fun k n => Complex.exp (-2 * π * I * k * n / N)

noncomputable def iWₙ {N: ℕ} : Matrix (Fin N) (Fin N) ℂ :=
  fun k n => (1/N) * Complex.exp (2 * π * I * k * n / N)

lemma mod_eq_mod_neg (m a : ℤ) : Int.mod (-a) m = -Int.mod (a) m := by
  rw [Int.mod_def, Int.mod_def, Int.neg_div, neg_sub', mul_neg, sub_neg_eq_add]

lemma cexp_sub_ne_one {N : ℕ} (k p : Fin N) (h : (k ≠ p)) :
    Complex.exp (2 * π * I * (k - p) / N) ≠ 1 := by
  by_cases hN : N = 0
  exfalso
  apply Fin.elim0 (by convert k; exact hN.symm)
  by_contra hg
  rw [Complex.exp_eq_one_iff] at hg
  obtain ⟨z, hz⟩ := hg
  rw [mul_div_assoc, mul_comm (z:ℂ) _, (mul_right_inj' two_pi_I_ne_zero),
      (div_eq_iff_mul_eq (Nat.cast_ne_zero.2 hN))] at hz
  norm_cast at hz
  apply_fun ( Int.mod · N) at hz
  simp only [Int.mul_mod_left, Int.subNatNat_eq_coe] at hz
  by_cases h1 : p ≤ k
  · rw [Int.mod_eq_of_lt, eq_comm, sub_eq_zero] at hz
    norm_cast at hz
    apply h (Fin.ext hz)
    simp only [sub_nonneg, Nat.cast_le, Fin.val_fin_le]
    exact h1
    rw [← Nat.cast_sub]
    norm_cast
    apply Nat.sub_lt_right_of_lt_add h1
    apply Nat.lt_add_right _
    apply Fin.is_lt
    exact_mod_cast h1
  · push_neg at h1
    rw [ ← neg_sub, mod_eq_mod_neg, eq_comm, neg_eq_zero, Int.mod_eq_of_lt, sub_eq_zero,
      eq_comm] at hz
    norm_cast at hz
    apply h (Fin.ext hz)
    simp only [neg_sub, sub_nonneg, Nat.cast_le, Fin.val_fin_le]
    apply le_of_lt h1
    rw [← Nat.cast_sub]
    norm_cast
    apply Nat.sub_lt_right_of_lt_add (le_of_lt h1)
    apply Nat.lt_add_right _
    apply Fin.is_lt
    apply le_of_lt
    exact_mod_cast h1
theorem iWₙ_mul_Wₙ_eq_one {N : ℕ} : iWₙ * (@Wₙ N) = 1 := by
  funext p q
  rw [mul_apply]
  unfold Wₙ iWₙ
  by_cases hN : N = 0
  · exfalso
    apply Fin.elim0 (by convert p; exact hN.symm)
  -- N ≠ 0
  simp_rw [mul_assoc (1/N:ℂ), ←Complex.exp_add, ←Finset.mul_sum, neg_mul, neg_div, ←sub_eq_add_neg,
    ← sub_div, mul_assoc (2*π*I), ← mul_sub, mul_comm (p:ℂ) _, ← mul_sub]
  have (a b c: Fin N) : cexp (2 * π * I * (a * (b - c)) / N) =  cexp (2 * π * I * (b - c) / N) ^ (a:ℕ) := by
    rw [← Complex.exp_nat_mul]
    ring_nf
  simp_rw [this]
  clear this
  by_cases h : p = q
  · simp_rw [h, sub_self, mul_zero, zero_div, Complex.exp_zero, one_pow, Fin.sum_const, nsmul_eq_mul,
      mul_one, one_apply_eq]
    apply div_mul_cancel₀
    simp only [ne_eq, Nat.cast_eq_zero]
    exact hN
  -- p ≠ q
  rw [one_apply_ne h, Fin.sum_univ_eq_sum_range, geom_sum_eq, ← Complex.exp_nat_mul,
      mul_div_cancel₀, one_div_mul_eq_div]
  rw [div_eq_zero_iff, div_eq_zero_iff]
  left
  left
  rw [sub_eq_zero, Complex.exp_eq_one_iff]
  use (p - q)
  norm_cast
  ring
  simp only [ne_eq, Nat.cast_eq_zero]
  exact hN
  apply cexp_sub_ne_one _ _ h

theorem inv_Wₙ {N: ℕ} : Wₙ⁻¹ = @iWₙ N := by
  rw [inv_eq_left_inv]
  exact iWₙ_mul_Wₙ_eq_one

noncomputable def instInvertibleWₙ {N: ℕ} : Invertible (@Wₙ N) :=
  invertibleOfLeftInverse  _ (@iWₙ N) (iWₙ_mul_Wₙ_eq_one)

lemma iWₙ_inv_def {N : ℕ} (k n : Fin N) :  Wₙ⁻¹ k n = (1/N) * Complex.exp (2 * π * I * k * n / N) := by
  rw [inv_Wₙ, iWₙ]

theorem eq_403 {N : ℕ} (k n : Fin N) :  Wₙ k n = Complex.exp (-2 * π * I * k * n / N) := rfl

noncomputable def dft {N: ℕ} (x: (Fin N) → ℂ) : (Fin N → ℂ) :=
  fun (k: Fin N) => ∑ (n : Fin N), (Wₙ k n) * (x n)

noncomputable def idft {N: ℕ} (X: (Fin N) → ℂ) : (Fin N → ℂ) :=
  fun (n: Fin N) => ∑ (k : Fin N), (Wₙ⁻¹ k n) * (X k)

theorem eq_404 {N : ℕ} (x : Fin N → ℂ) (k : Fin N): (dft x) k =  ∑ (n : Fin N), (Wₙ k n) * (x n) := rfl

theorem eq_405 {N : ℕ} (X : Fin N → ℂ) (n : Fin N): (idft X) n =  ∑ (k : Fin N), (Wₙ⁻¹ k n) * (X k) := by rfl

theorem eq_406 {N : ℕ} (x : Fin N → ℂ) : (dft x) = Matrix.mulVec Wₙ x := by rfl

theorem eq_407 {N : ℕ} (X : Fin N → ℂ) : (idft X) = Matrix.mulVec Wₙ⁻¹ X := by
  funext z
  unfold idft
  simp_rw [Matrix.mulVec, dotProduct, iWₙ_inv_def]
  rw [Fintype.sum_congr]
  intro a
  simp_rw [mul_assoc (1/N:ℂ)]
  rw [mul_eq_mul_left_iff]
  left
  ring_nf

theorem eq_408 {N : ℕ} : Wₙ⁻¹ = (1 /N:ℂ) • (@Wₙ N)ᴴ  := by
  rw [inv_Wₙ]
  unfold Wₙ iWₙ
  funext a b
  rw [smul_apply, smul_eq_mul, mul_eq_mul_left_iff, conjTranspose_apply, star_def, ← Complex.exp_conj]
  left
  simp only [neg_mul, map_div₀, map_neg, _root_.map_mul, map_ofNat, conj_I, mul_neg, map_natCast,
    neg_neg, Complex.conj_ofReal]
  congr 2
  ring
  done

theorem eq_409 {N : ℕ} : (@Wₙ N) * Wₙᴴ = (N:ℂ) • 1 := by
  by_cases hN : N ≠ 0
  · apply_fun (fun x => (1/N:ℂ) • x)
    dsimp
    rw [← Matrix.mul_smul, ← eq_408, Matrix.mul_nonsing_inv, one_div, smul_smul, inv_mul_cancel,
      one_smul]
    exact_mod_cast hN
    let _ := @instInvertibleWₙ N
    apply isUnit_det_of_invertible
    apply smul_right_injective
    rw [ne_eq, one_div, inv_eq_zero, Nat.cast_eq_zero]
    apply hN
  · rw [ne_eq, not_not] at hN
    funext a
    exfalso
    apply Fin.elim0 (by convert a; exact hN.symm)

def Matrix.conj [Star R](M : Matrix m n R) := Mᴴᵀ --M.map star

theorem eq_410 {N : ℕ} :  Matrix.conj (@Wₙ N) =  Wₙᴴ := by
  unfold Matrix.conj
  funext a b
  simp_rw [transpose_apply, conjTranspose_apply, star_inj, eq_403]
  ring_nf

lemma twiddle_neg_half_cycle_eq_neg' {N: ℕ} (hN1: 1 < N):
  Complex.exp (-2 * π * I / N)^((N:ℂ)/(2:ℂ)) = -1 := by
  have hN : N ≠ 0 := Nat.pos_iff_ne_zero.1 (lt_trans zero_lt_one hN1)
  by_cases hN2: N = 2
  · simp_rw [hN2, neg_mul, neg_div, Nat.cast_ofNat]
    rw [div_self two_ne_zero, cpow_one, mul_assoc, mul_div_cancel_left₀]
    rw [Complex.exp_neg, ← inv_neg_one]
    apply inv_inj.2
    exact exp_pi_mul_I
    exact two_ne_zero
  have hNg2 : 2 < N := by omega
  rw [← Complex.exp_pi_mul_I, cpow_def_of_ne_zero, Complex.exp_eq_exp_iff_exists_int]
  use (-1:ℤ)
  rw [Complex.log_exp]
  ring_nf
  rw [mul_assoc, mul_inv_cancel, mul_one]
  exact_mod_cast hN
  rotate_right
  exact Complex.exp_ne_zero _
  all_goals (simp only [neg_mul, div_natCast_im, neg_im, mul_im, mul_re, re_ofNat, ofReal_re, im_ofNat,
    ofReal_im, mul_zero, sub_zero, I_im, mul_one, zero_mul, add_zero, I_re, neg_div, neg_lt_neg_iff])
  rotate_left
  apply le_of_lt
  apply lt_trans _ pi_pos
  apply neg_lt_zero.2 _
  apply div_pos two_pi_pos (Nat.cast_pos.2 (Nat.pos_iff_ne_zero.2 hN))
  rw [div_lt_iff, mul_comm]
  apply (mul_lt_mul_iff_of_pos_left pi_pos).2
  exact_mod_cast hNg2
  apply (lt_trans zero_lt_one _)
  exact_mod_cast hN1

theorem eq_411 {N : ℕ}{h2: 2 ≤ N} {m: ℤ} :
    let Wₙ := Complex.exp (-2 * π * I  / N)
    Wₙ ^ (m + N/2: ℂ)  = -Wₙ ^ (m:ℂ)  := by
  dsimp
  rw [Complex.cpow_add]
  simp only [Complex.cpow_intCast]
  rw [← neg_one_mul ((Complex.exp (-2 * π * I / N:ℂ))^m), mul_comm, mul_left_inj']
  exact twiddle_neg_half_cycle_eq_neg' h2
  rw [← Complex.exp_int_mul]
  exact Complex.exp_ne_zero _
  exact Complex.exp_ne_zero _

def shiftk {N: ℕ} (k: Fin N):(Fin N → Fin N)
  := fun n : (Fin N) => (n + k)

def shiftk_equiv {N: ℕ} {hN: NeZero N} (k: Fin N) : (Fin N) ≃ (Fin N) :=
{
  toFun := @shiftk N  (-k)
  invFun := @shiftk N (k)
  left_inv := by (intro x; rw [shiftk, shiftk]; ring)
  right_inv := by (intro x; rw [shiftk, shiftk]; ring)
}

lemma Wₙ_add {N : ℕ} (a x y : Fin N): Wₙ a (x + y) = Wₙ a x * Wₙ a y := by
  have hN : N ≠ 0 := by
    by_contra hc
    apply Fin.elim0 (by convert a; exact hc.symm);
  simp_rw [eq_403, ← Complex.exp_add, neg_mul, neg_div, ← neg_add]
  rw [Complex.exp_eq_exp_iff_exists_int]
  let z:ℤ := ((↑x + ↑y)/N)
  set w:ℤ := a*z with hw
  use w
  rw [neg_add_eq_sub, mul_comm (w:ℂ)]
  simp_rw [mul_assoc (2 * π * I), ← add_div, ← mul_add, mul_div_assoc, ← mul_sub]
  rw [← mul_neg]
  rw [mul_eq_mul_left_iff]
  rw [hw]
  left
  norm_cast
  -- refine neg_inj.mpr ?e_z.a
  -- rw [← add_div]
  -- simp_rw [mul_assoc (2 * π * I), ← mul_add]
  -- rw [mul_right_inj', mul_eq_mul_left_iff]
  -- left
  -- norm_cast
  -- rw [Fin.coe_sub]
  sorry
  -- exact two_pi_I_ne_zero
  -- exact Nat.cast_ne_zero.mpr hN

theorem eq_412 {N : ℕ}(hN: NeZero N)(t : Fin N → ℂ) :
  Matrix.circulant t = Wₙ⁻¹ * Matrix.diagonal (dft t) * Wₙ := by
  let _ := @instInvertibleWₙ N
  apply_fun (fun x => Wₙ * x)
  dsimp
  rw [mul_assoc, Matrix.mul_nonsing_inv_cancel_left]
  funext a b
  rw [mul_apply, mul_apply]
  simp only [diagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp only [circulant_apply]
  unfold dft
  rw [Finset.sum_mul]
  conv =>
    rhs
    congr
    rfl
    ext
    rw [mul_comm, ← mul_assoc, mul_comm (Wₙ a b)]
    rfl
  rw [← Equiv.sum_comp (@shiftk_equiv N hN (-b))]
  rw [shiftk_equiv]
  dsimp
  simp_rw [shiftk, neg_neg, add_sub_cancel_right, Wₙ_add]
  apply isUnit_det_of_invertible
  apply Matrix.mul_right_injective_of_invertible


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

theorem eq_417 (A : Matrix m m ℂ) : A.IsHermitian → (sorry : Prop) :=
  sorry

/-! ## Idempotent Matrices -/


section

variable (A : Matrix m m R) (B : Matrix m m R)

theorem eq_418 (hA : IsIdempotentElem A) (n : ℕ) (hn : n ≠ 0) : A ^ n = A := by
  cases' n with n
  · cases hn rfl
  · exact hA.pow_succ_eq n

theorem eq_419 (hA : IsIdempotentElem A) : IsIdempotentElem (1 - A) :=
  hA.one_sub

theorem eq_420 [StarRing R] (hA : IsIdempotentElem A) : IsIdempotentElem Aᴴ :=
  sorry

theorem eq_421 [StarRing R] (hA : IsIdempotentElem A) : IsIdempotentElem (1 - Aᴴ) :=
  sorry

theorem eq_422 (hA : IsIdempotentElem A) (hB : IsIdempotentElem B) (h : Commute A B) :
    IsIdempotentElem (A * B) :=
  hA.mul_of_commute h hB

theorem eq_423 (hA : IsIdempotentElem A) : sorry = trace A :=
  sorry

theorem eq_424 (hA : IsIdempotentElem A) : A * (1 - A) = 0 := by
  -- porting note: was `simp [mul_sub, ← Matrix.mul_eq_mul, hA.eq]`
  rw [Matrix.mul_sub, Matrix.mul_one, hA.eq, sub_self]

theorem eq_425 (hA : IsIdempotentElem A) : (1 - A) * A = 0 := by
   -- porting note: was `simp [sub_mul, ← Matrix.mul_eq_mul, hA.eq]`
  rw [Matrix.sub_mul, Matrix.one_mul, hA.eq, sub_self]

theorem eq_426 : (sorry : Prop) :=
  sorry

theorem eq_427 : (sorry : Prop) :=
  sorry

end

/-! ### Nilpotent -/


theorem eq_428 : (sorry : Prop) :=
  sorry

/-! ### Unipotent -/


theorem eq_429 : (sorry : Prop) :=
  sorry

/-! ## Orthogonal matrices -/


/-! ### Ortho-Sym -/


theorem eq_430 : (sorry : Prop) :=
  sorry

theorem eq_431 : (sorry : Prop) :=
  sorry

theorem eq_432 : (sorry : Prop) :=
  sorry

theorem eq_433 : (sorry : Prop) :=
  sorry

/-! ### Ortho-Skew -/


theorem eq_434 : (sorry : Prop) :=
  sorry

theorem eq_435 : (sorry : Prop) :=
  sorry

theorem eq_436 : (sorry : Prop) :=
  sorry

theorem eq_437 : (sorry : Prop) :=
  sorry

/-! ### Decomposition -/


theorem eq_438 : (sorry : Prop) :=
  sorry

/-! ## Positive Definite and Semi-definite Matrices -/


/-! ### Definitions -/


theorem eq_439 (A : Matrix n n ℝ) : A.PosDef ↔ ∀ x ≠ 0, x ⬝ᵥ A.mulVec x > 0 :=
  sorry

theorem eq_440 (A : Matrix n n ℝ) : A.PosSemidef ↔ ∀ x, x ⬝ᵥ A.mulVec x ≥ 0 :=
  sorry

/-! ### Eigenvalues -/


theorem eq_441 : (sorry : Prop) :=
  sorry

/-! ### Trace -/


theorem eq_442 : (sorry : Prop) :=
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

-- note this is 0-indexed not 1-indexed
theorem eq_443 :
    stdBasisMatrix (1 : Fin 4) (2 : Fin 4) 1 =
      !![0, 0, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, 0;
         0, 0, 0, 0] := by
  decide

/-! ### Swap and Zeros -/

theorem eq_444 (A : Matrix n m R) (i : m) (j : p) :
    A * stdBasisMatrix i j (1 : R) = updateColumn 0 j (A · i)  :=
  sorry

theorem eq_445 (i : p) (j : n) (A : Matrix n m R) :
    stdBasisMatrix i j (1 : R) * A = updateRow 0 i (A j)  :=
  sorry

/-! ### Rewriting product of elements -/


theorem eq_446 (A : Matrix l m R) (B : Matrix n p R) (k i j l) :
    A k i * B j l = (A * stdBasisMatrix i j (1 : R) * B) k l := by
  sorry

theorem eq_447 (A : Matrix l m R) (B : Matrix n p R) (k i j l) :
    A i k * B l j = (Aᵀ * stdBasisMatrix i j (1 : R) * Bᵀ) k l := by
  rw [←eq_446]; rfl

theorem eq_448 (A : Matrix l m R) (B : Matrix n p R) (k i j l) :
    A i k * B j l = (Aᵀ * stdBasisMatrix i j (1 : R) * B) k l := by
  rw [←eq_446]; rfl

theorem eq_449 (A : Matrix l m R) (B : Matrix n p R) (k i j l) :
    A k i * B l j = (A * stdBasisMatrix i j (1 : R) * Bᵀ) k l := by
  rw [←eq_446]; rfl

/-! ### Properties of the Singleentry Matrix -/


/-! ### The Singleentry Matrix in Scalar Expressions -/


theorem eq_450 (A : Matrix n m R) :
    trace (A * stdBasisMatrix i j (1 : R)) = Aᵀ i j ∧
    trace (stdBasisMatrix i j (1 : R) * A) = Aᵀ i j :=
  sorry

theorem eq_451 (A : Matrix n n R) (i : n) (j : m) (B : Matrix m n R) :
    trace (A * stdBasisMatrix i j (1 : R) * B) = (Aᵀ * Bᵀ) i j :=
  sorry

theorem eq_452 (A : Matrix n n R) (j : n) (i : m) (B : Matrix m n R) :
    trace (A * stdBasisMatrix j i (1 : R) * B) = (B * A) i j :=
  sorry

/-- The cookbook declares incompatible dimensions here; weassume the matrices are supposed to be
square. -/
theorem eq_453 (A : Matrix n n R) (i : n) (j : n) (B : Matrix n n R) :
    trace (A * stdBasisMatrix i j (1 : R) * stdBasisMatrix i j (1 : R) * B) =
      diagonal (diag (Aᵀ * Bᵀ)) i j :=
  sorry

theorem eq_454 (A : Matrix n n R) (i : n) (j : m) (B : Matrix m n R) (x : n → R) :
    x ⬝ᵥ (A * stdBasisMatrix i j (1 : R) * B).mulVec x = (Aᵀ * vecMulVec x x * Bᵀ) i j :=
  sorry

/-- The cookbook declares incompatible dimensions here; weassume the matrices are supposed to be
square. -/
theorem eq_455  (A : Matrix n n R) (i : n) (j : n) (B : Matrix n n R) (x : n → R) :
    x ⬝ᵥ (A * stdBasisMatrix i j (1 : R) * stdBasisMatrix i j (1 : R) * B).mulVec x =
      diagonal (diag (Aᵀ * vecMulVec x x * Bᵀ)) i j :=
  sorry

/-! ### Structure Matrices -/


theorem eq_456 : (sorry : Prop) :=
  sorry

theorem eq_457 : (sorry : Prop) :=
  sorry

theorem eq_458 : (sorry : Prop) :=
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


theorem eq_463 : (sorry : Prop) :=
  sorry

theorem eq_464 : (sorry : Prop) :=
  sorry

/-! ## Toeplitz Matrices -/


theorem eq_465 : (sorry : Prop) :=
  sorry

theorem eq_466 : (sorry : Prop) :=
  sorry

theorem eq_467 : (sorry : Prop) :=
  sorry

theorem eq_468 : (sorry : Prop) :=
  sorry

theorem eq_469 : (sorry : Prop) :=
  sorry

/-! ### Properties of Toeplitz Matrices -/


/-! ## Transition matrices -/


theorem eq_470 : (sorry : Prop) :=
  sorry

theorem eq_471 : (sorry : Prop) :=
  sorry

theorem eq_472 : (sorry : Prop) :=
  sorry

theorem eq_473 : (sorry : Prop) :=
  sorry

theorem eq_474 : (sorry : Prop) :=
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
      of ![(Pi.single 1 1 : Fin 3 → R), Pi.single 0 1, Pi.single 2 1] := by ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem eq_478 (e : Equiv.Perm m) :
    e.toPEquiv.toMatrix * e.toPEquiv.toMatrixᵀ = (1 : Matrix m m R) := by
  rw [← PEquiv.toMatrix_symm, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_symm, ←
    Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

theorem eq_479 : (sorry : Prop) :=
  sorry

/-! ### Translation, Shift or Lag Operators -/


theorem eq_480 : (sorry : Prop) :=
  sorry

theorem eq_481 : (sorry : Prop) :=
  sorry

theorem eq_482 : (sorry : Prop) :=
  sorry

theorem eq_483 : (sorry : Prop) :=
  sorry

theorem eq_484 : (sorry : Prop) :=
  sorry

/-! ## Vandermonde Matrices -/


theorem eq_485 {n : ℕ} (v : Fin n → R) (i j : Fin n) : vandermonde v i j = v i ^ (j : ℕ) :=
  vandermonde_apply _ _ _

theorem eq_486 {n : ℕ} (v : Fin n → R) :
    det (vandermonde v) = ∏ i : Fin n, ∏ j in Finset.Ioi i, (v j - v i) :=
  det_vandermonde _

end MatrixCookbook
