import data.complex.basic
import linear_algebra.matrix.hermitian
import linear_algebra.matrix.symmetric
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.adjugate
import linear_algebra.vandermonde
import linear_algebra.matrix.circulant
import linear_algebra.matrix.schur_complement
import data.complex.exponential
import analysis.special_functions.trigonometric.basic
import data.matrix.basic
import data.matrix.reflection
import algebra.geom_sum

/-! # Special Matrices -/

variables {R : Type*} {l m n p q r : Type*}
variables [fintype l] [fintype m] [fintype n] [fintype p] [fintype q] [fintype r]
variables [decidable_eq l] [decidable_eq m] [decidable_eq n] [decidable_eq p] [decidable_eq q] [decidable_eq r]
variables [field R]

open matrix
open_locale matrix big_operators complex_conjugate
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

lemma eq_401 (A₁₁ : matrix m m R) (A₂₂ : matrix n n R)
  [h1: invertible A₁₁] [h2: invertible (A₂₂)] :
  (from_blocks A₁₁ 0 0 A₂₂)⁻¹ = from_blocks A₁₁⁻¹ 0 0 A₂₂⁻¹ := 
begin
  apply inv_eq_right_inv,
  rw from_blocks_multiply,
  simp only [mul_inv_of_invertible, matrix.zero_mul, 
  add_zero, matrix.mul_zero, zero_add, from_blocks_one],
end
lemma eq_402 (A₁₁ : matrix m m R) (A₂₂ : matrix n n R) :
  det (from_blocks A₁₁ 0 0 A₂₂) = det A₁₁ * det A₂₂ := det_from_blocks_zero₁₂ _ _ _

/-! ### Schur complement -/

/-! ## Discrete Fourier Transform Matrix, The -/

/- lemma eq_403 : sorry := sorry
-- Perhaps we can write eq 403 as a definition -/


section dft_matrices
open_locale real matrix big_operators
open matrix
open equiv equiv.perm finset
open complex

-- Forward DFT Matrix
noncomputable def Wₙ {N: ℕ}: matrix (fin N) (fin N) ℂ :=
λ k n, exp(-2 * π * I * k * n / N)

-- Conjugate DFT Matrix: Just the complex conjugate
noncomputable def sWₙ {N: ℕ} : matrix (fin N) (fin N) ℂ :=
λ k n, exp(2 * π * I * k * n / N)

-- Inverse DFT Matrix: Conjugate divided by N
noncomputable def iWₙ {N: ℕ} : matrix (fin N) (fin N) ℂ := 
(1/N:ℂ)•(sWₙ)

lemma exp_pow_s {N:ℕ}{hN: ne_zero N} (i k n: fin N):
  exp(2 * π * I * i * (k - n) / N) = 
    exp(2 * π * I * (k - n) / N) ^ (i:ℕ) := 
begin
  have : 2 * ↑π * I * i * (k - n) / N = i * (2 * π * I * (k - n) / N), {
    by ring,
  },
  rw this, rw coe_coe,
  rw exp_nat_mul _ ↑i,
end

lemma Wkn_dot_iWKn_offdiag {N:ℕ} {hN: N ≠ 0} 
  {k n: fin N} {h_k_ne_n: ¬(k = n)} :
    ∑ (i : fin N), exp(2 * π * I * i * (k - n) / N) = 0 := 
begin
  have hN_ne_zero : (↑N:ℂ) ≠ 0, 
    by { simp only [ne.def, nat.cast_eq_zero], exact hN,},

  conv_lhs { 
    apply_congr, skip,
     rw @exp_pow_s N (ne_zero_iff.2 hN) x k n,
  },
  rw fin.sum_univ_eq_sum_range,
  rw geom_sum_eq, 
  simp only [_root_.div_eq_zero_iff],
  left,
  rw sub_eq_zero, 

  simp_rw [← complex.exp_nat_mul, mul_comm ↑N _],
  rw [div_mul_cancel, mul_comm],

  rw complex.exp_eq_one_iff, use (↑k:ℤ) - ↑n,
  simp only [coe_coe, int.cast_sub, int.cast_coe_nat], 
  exact hN_ne_zero,

  by_contra hc,
  rw complex.exp_eq_one_iff at hc,
  cases hc with m hm,
  set α := 2*↑π*I,
  set β:ℂ := ↑k - ↑n,
  
  rw [mul_comm _ α] at hm, 
  rw mul_div_assoc at hm,
  rw (mul_right_inj' two_pi_I_ne_zero) at hm,
  
  change β with ↑k - ↑n at hm,
  simp only [coe_coe] at hm,
  
  set ak : ℕ := ↑k,
  set an : ℕ := ↑n,
  rw (div_eq_iff_mul_eq hN_ne_zero) at hm,
  rw @coe_coe ℕ ℤ ℂ _ _ ak at hm,
  rw @coe_coe ℕ ℤ ℂ _ _ an at hm,
  rw @coe_coe ℕ ℤ ℂ _ _ N at hm,
  set aN : ℤ := ↑N,
  rw ← int.cast_sub (↑ak) (↑an) at hm,
  rw ← int.cast_mul m aN at hm,
  rw int.cast_inj at hm,
  apply_fun (% N) at hm, 
  simp only [int.mul_mod_left] at hm,
  
  replace hm := hm.symm,
  
  rw ← int.mod_eq_mod_iff_mod_sub_eq_zero at hm,
  rw int.mod_eq_of_lt at hm,
  rw int.mod_eq_of_lt at hm,
  rw int.coe_nat_eq_coe_nat_iff at hm,
  change ak with ↑k at hm, change an with ↑n at hm,
  rw fin.coe_eq_coe at hm,
  exact h_k_ne_n hm,
  simp only [nat.cast_nonneg],
  simp only [nat.cast_lt, fin.is_lt],
  simp only [nat.cast_nonneg],
  simp only [nat.cast_lt, fin.is_lt],
end

lemma Wₙ_mul_sWₙ {N: ℕ} {hN: ne_zero N}: 
  (Wₙ: matrix (fin N) (fin N) ℂ)⬝sWₙ = (N:ℂ)•1 := 
begin
  rw Wₙ, rw sWₙ,
  funext k n,
  rw pi.smul_apply, rw pi.smul_apply,
  rw matrix.mul, dsimp, rw dot_product,
  rw neg_mul,
  rw neg_mul,
  set η := 2*↑π*I,
  conv_lhs {  
    apply_congr, skip, rw mul_comm,
    rw ← exp_add, rw ← add_div,
    rw neg_mul, rw neg_mul,rw ← sub_eq_add_neg, 
    rw mul_assoc, rw mul_assoc η _ _,
    rw ← mul_sub, rw mul_comm ↑↑k, rw ← mul_sub, rw ← mul_assoc,
  },
  by_cases hkn: (n = k), {
    rw hkn, rw one_apply_eq, rw sub_self,
    simp only [mul_zero, zero_div, exp_zero, 
    sum_const, card_fin, nat.smul_one_eq_coe, mul_one],
  }, { -- k ≠ n
    rw ← ne.def at hkn,
    rw one_apply_ne' hkn, rw mul_zero,
    apply Wkn_dot_iWKn_offdiag,
    exact ne_zero_iff.1 hN, apply hkn,
  },
end

lemma inverse_Wₙ {N: ℕ} {hN: ne_zero N}: 
  (Wₙ: matrix (fin N) (fin N) ℂ)⁻¹ = (1/N:ℂ)•(λ k n, exp(2 * π * I * k * n / N)) :=
begin
  have hNz: (N:ℂ) ≠ 0, {rw nat.cast_ne_zero, exact (ne_zero_iff.1 hN), },
  apply inv_eq_right_inv, rw matrix.mul_smul,
  apply_fun (has_smul.smul (N:ℂ)), rw one_div, rw smul_inv_smul₀,
  rw ← sWₙ,
  apply @Wₙ_mul_sWₙ N hN,
  exact hNz,
  apply smul_right_injective,
  exact hNz,
end

lemma Wₙ_mul_iWₙ_eq_one {N: ℕ} {hN: ne_zero N}: 
  (Wₙ: matrix (fin N) (fin N) ℂ)⬝iWₙ = 1 :=
begin
  have hNz: (N:ℂ) ≠ 0, 
    {rw nat.cast_ne_zero, exact (ne_zero_iff.1 hN), },

  rw iWₙ, rw matrix.mul_smul, rw one_div, rw inv_smul_eq_iff₀,
   apply @Wₙ_mul_sWₙ N hN,
  assumption,
end

lemma Wₙ_symmetric {N: ℕ} {hN: ne_zero N} :
  (Wₙ: matrix (fin N) (fin N) ℂ)ᵀ = Wₙ :=
begin
  funext k n,
  rw transpose_apply, rw Wₙ,
  ring_nf,
end

lemma sWₙ_symmetric {N: ℕ} {hN: ne_zero N} :
  (sWₙ: matrix (fin N) (fin N) ℂ)ᵀ = sWₙ :=
begin
  funext k n,
  rw transpose_apply, rw sWₙ,
  ring_nf,
end

lemma iWₙ_mul_Wₙ_eq_one {N: ℕ} {hN: ne_zero N}: 
  iWₙ⬝(Wₙ: matrix (fin N) (fin N) ℂ) = 1 :=
begin
  have hNz: (N:ℂ) ≠ 0, 
    {rw nat.cast_ne_zero, exact (ne_zero_iff.1 hN), },

  rw iWₙ, rw matrix.smul_mul, rw one_div, rw inv_smul_eq_iff₀,
  apply_fun (transpose), 
  rw transpose_mul, rw Wₙ_symmetric,
  rw sWₙ_symmetric, rw transpose_smul, rw transpose_one,
  apply Wₙ_mul_sWₙ,
  assumption', 
  rintros x y hxy,funext k n,
  rw ← matrix.ext_iff at hxy,
  specialize hxy n k, 
  rw transpose_apply at hxy,
  rw transpose_apply at hxy, exact hxy,
end

lemma inv_Wₙ {N: ℕ} {hN: ne_zero N} :
  (Wₙ: matrix (fin N) (fin N) ℂ)⁻¹ = iWₙ := 
begin
  rw inverse_Wₙ,
  rw iWₙ, rw sWₙ, exact hN,
end

lemma twiddle_comm' {N: ℕ}(k n: fin N) :
  Wₙ k n = Wₙ n k := begin
  rw Wₙ, dsimp, ring_nf,
end

lemma twiddle_sum {N: ℕ}{hN: ne_zero N}(k m n: fin N) :
  Wₙ k m * Wₙ k n  = Wₙ k (m + n) := 
begin
  rw Wₙ, dsimp, 
  -- repeat {rw Wkn},
  have hNz: (↑N:ℂ) ≠ 0, {
    rw nat.cast_ne_zero, rwa ne_zero_iff at hN, 
  },
  rw neg_mul,
  rw neg_mul,
  rw neg_mul,
  rw neg_mul,
  rw neg_mul,
  rw neg_mul,
  rw neg_div,
  rw neg_div,
  rw neg_div,
  rw exp_neg,
  rw exp_neg,
  rw exp_neg,
  rw ← mul_inv, rw inv_eq_iff_eq_inv, rw inv_inv,

  rw ← exp_add, 
  rw exp_eq_exp_iff_exists_int,
  let a:ℤ := ((↑m + ↑n)/N),
  let w:ℤ := k*a,
  use w, 
  
  rw ← add_div, rw ← mul_add (2 * ↑π * I * ↑↑k),
  set α := (2 * ↑π * I),
  rw mul_comm _ α, 
  rw mul_assoc, rw mul_div_assoc,
  rw mul_assoc α _ _, rw mul_div_assoc α,
  rw ←  mul_add α,
  rw mul_right_inj' two_pi_I_ne_zero,
  rw div_eq_iff hNz, rw add_mul, 
  rw div_mul_cancel _ hNz ,
  change w with k*a,
  rw int.cast_mul, simp only [coe_coe, int.cast_coe_nat],
  rw ← coe_coe,
  rw mul_assoc,
  rw ← mul_add (↑k:ℂ),
  by_cases hk: (↑k:ℂ) ≠ 0, {
    -- rw mul_eq_mul_left_iff, left,
    rw mul_right_inj' hk,
    norm_cast, rw fin.coe_add,
    change a with ((↑m + ↑n)/N),
    simp only [coe_coe, int.cast_coe_nat], norm_cast,
    rw nat.mod_add_div' (↑m + ↑n) N,
  }, {
    simp only [not_not] at hk,
    rw hk, rw zero_mul, rw zero_mul,
  },
end

lemma conj_Wₙ {N: ℕ} {hN: ne_zero N}: 
  (Wₙ: matrix (fin N) (fin N) ℂ)ᵀᴴ = sWₙ :=
begin
  rw @Wₙ_symmetric N hN, funext,
  rw Wₙ, rw sWₙ, dsimp, rw ← exp_conj,
  rw neg_mul, rw neg_mul, rw mul_comm (2*↑π:ℂ), rw ← neg_mul,
  rw mul_assoc, rw mul_assoc, rw mul_div_assoc,
  rw star_ring_end_apply, rw star_mul', rw ← star_ring_end_apply,
  rw conj_neg_I,
  rw exp_eq_exp_iff_exists_int, use 0, 
  simp only [coe_coe, is_R_or_C.star_def, map_div₀, 
  _root_.map_mul, is_R_or_C.conj_bit0, _root_.map_one, is_R_or_C.conj_of_real,
  map_nat_cast, algebra_map.coe_zero, zero_mul, add_zero],
  ring_nf,

end

-- eq_404
noncomputable def dft {N: ℕ} (x: (fin N) → ℂ) : (fin N → ℂ) := 
λ (k: fin N), ∑ (n : fin N), (Wₙ k n) * (x n)

-- eq_405
noncomputable def idft {N: ℕ} (X: (fin N) → ℂ) : (fin N → ℂ) := 
λ (k: fin N), (1/N)*(∑ (n : fin N),  (Wₙ) (-k) n * (X n))

lemma eq_406 {N: ℕ} (x: fin N → ℂ) : 
dft x = matrix.mul_vec Wₙ x := 
by {funext k, rw [dft], refl}

lemma eq_407 {N: ℕ} {hN: ne_zero N} (X: fin N → ℂ) : 
idft X = (matrix.mul_vec (Wₙ⁻¹) X) := 
begin
  have hNz: (N:ℂ) ≠ 0, {rw nat.cast_ne_zero, exact (ne_zero_iff.1 hN), },
  funext k, rw idft, rw inverse_Wₙ, rw Wₙ, dsimp, rw mul_vec, rw dot_product,
  dsimp, rw mul_sum, 
  rw neg_mul,
  rw neg_mul, 
  rw neg_mul, rw ← mul_neg, 
  set η := 2*↑π*I,
  by_cases hk: (k) = 0, {
    rw hk, simp only [neg_zero, fin.coe_zero, char_p.cast_eq_zero, 
    mul_zero, zero_mul, zero_div, exp_zero, one_mul, mul_one],
  },{ -- 1 ≤ k < N,
    rw fin.coe_neg k,
    have khgt: ↑(0:(fin N)) < (↑k:ℕ), by {
      rw ← fin.lt_iff_coe_lt_coe,
      rw ← ne.def at hk,
      exact (fin.pos_iff_ne_zero k).2 hk,
    },
    have hNk: N - ↑k < N, {
      exact (nat.sub_lt_of_pos_le ↑k N khgt) (le_of_lt (fin.is_lt k)),
    },
    rw (nat.mod_eq_of_lt hNk),
    rw nat.cast_sub, rw neg_sub,
    conv_lhs {
      apply_congr, skip,
      rw mul_sub, rw sub_mul,rw sub_div,
      rw mul_assoc _ ↑N ↑↑x, rw mul_comm ↑N ↑↑x,
      rw ← mul_assoc _ ↑↑x ↑N, rw mul_div_cancel _ hNz,
      rw exp_sub, rw mul_comm η ↑↑x, rw exp_nat_mul_two_pi_mul_I,
      rw div_one, rw ← mul_assoc _ _ (X x),
    },
    simp only [fin.is_le'],
  },
  assumption',
end

lemma eq_408 {N: ℕ} {hN: ne_zero N} :   
  (Wₙ: matrix (fin N) (fin N) ℂ )⁻¹ = (N:ℂ)⁻¹ • sWₙ :=
begin
  rw inverse_Wₙ, rw inv_eq_one_div,
  rw sWₙ,
  exact hN,
end

lemma eq_409 {N: ℕ} {hN: N ≠ 0} : 
(Wₙ: matrix (fin N) (fin N) ℂ) ⬝ (sWₙ) =  (N:ℂ)•(1) := 
begin
  apply Wₙ_mul_sWₙ,
  exact ne_zero_iff.2 hN,
end

lemma eq_410 {N: ℕ} : 
(star Wₙ : matrix (fin N) (fin N) ℂ) = Wₙᴴ :=
begin
  unfold star,
end

lemma two_pi_I_by_N_piInt_pos {N : ℕ}
  (h2 : 2 < N) :
  (2 * ↑π * I / ↑N).im < π :=
begin
  have hNlt0 : 0 < (N:ℝ), by {
    simp only [nat.cast_pos],
    linarith,
  },
  have : (2) * ↑π * I / ↑N = (((2) * ↑π / ↑N)) * I, by {ring,},
  rw this, rw mul_I_im,

  have : ((2 * ↑π) / ↑N:ℂ).re = ((2 * π) / ↑N) , 
  by {norm_cast,}, rw this,

  rw div_lt_iff hNlt0, rw mul_comm, 
  rw mul_lt_mul_left real.pi_pos,
  norm_cast, exact h2,
end

lemma two_pi_I_by_N_piInt_neg {N : ℕ}
  (h2 : 2 < N) :
  -π < ((2) * ↑π * I / ↑N).im :=
begin
  have : (2) * ↑π * I / ↑N = (((2) * ↑π / ↑N)) * I, by {ring,},
  rw this, rw mul_I_im,

  have : ((2 * ↑π) / ↑N:ℂ).re = ((2 * π) / ↑N) , 
  by {norm_cast,}, rw this,
  have neg_pi_lt_zero: -π < 0, {
    exact neg_lt_zero.2 real.pi_pos,
  },
  set η : ℝ := ↑N,
  have zero_lt_η: 0 < η,{
    change η with ↑N,
    simp only [nat.cast_pos],
    linarith,
  },
  have pi_div_N_lt_zero: 0 < 2*π/η, {
    exact div_pos real.two_pi_pos zero_lt_η,
  },
  rw lt_div_iff zero_lt_η, 
  rw neg_mul, rw mul_comm, rw ← neg_mul, 
  rw mul_lt_mul_right real.pi_pos,
  rw neg_lt_iff_pos_add',
  change η with ↑N,
  exact add_pos zero_lt_η zero_lt_two,
end


lemma twiddle_neg_half_cycle_eq_neg' {N: ℕ} {hN: 2 ≤ N}:
  exp(-2 * π * I / N)^((N:ℂ)/(2:ℂ)) = 
  -1 :=
begin
  by_cases h2: (N = 2),
  rw h2, ring_nf,
  have: (1/(2:ℂ)*↑2) = 1, by {
    simp only [one_div, nat.cast_bit0, 
    algebra_map.coe_one,
     inv_mul_cancel_of_invertible],
  },
  rw this, simp only [cpow_one], rw exp_neg,
  rw mul_comm, rw exp_pi_mul_I,
  norm_num,
  rw le_iff_lt_or_eq at hN,
  cases hN with hNlt2 hNeq2,
  rw cpow_def_of_ne_zero,
  rw log_exp,
  rw div_mul,
  set η:ℂ := ↑N,
  have hη: η ≠ 0, 
    by {simp only [nat.cast_ne_zero], linarith,},

  rw div_div_cancel' hη, ring_nf,
  rw mul_comm, rw exp_neg,
  rw exp_pi_mul_I, norm_num,
  rw neg_mul, rw neg_mul, rw neg_div, rw neg_im,
  rw neg_lt_neg_iff,
  exact two_pi_I_by_N_piInt_pos hNlt2,
  
  rw neg_mul, rw neg_mul, rw neg_div, rw neg_im,
  rw neg_le,
  exact (le_of_lt (two_pi_I_by_N_piInt_neg hNlt2)),
  exact exp_ne_zero ((-2) * π * I / N),
  exfalso, exact h2 hNeq2.symm,
end


lemma eq_411 {N: ℕ}{h2: 2 ≤ N} {m: ℤ} : 
  let Wₙ := complex.exp(-2 * π * I  / N) in
  Wₙ ^ (m + N/2: ℂ)  = -Wₙ ^ (m:ℂ)  := 
begin
  dsimp only,
  set α := exp(- 2 * π * I / N),
  rw complex.cpow_add,
  simp only [cpow_int_cast],
  rw ← neg_one_mul, rw mul_comm,
  rw mul_left_inj',
  apply twiddle_neg_half_cycle_eq_neg',
  exact h2,
  rw ← exp_int_mul, ring_nf,
  exact exp_ne_zero (-(2 * (↑N)⁻¹ * I * ↑π * ↑m)),
  exact exp_ne_zero (- 2 * π * I / N),
end

def shiftk {N: ℕ}{hN: ne_zero N} (k: fin N):(fin N → fin N) 
  := λ n: (fin N), (n + k)

def shiftk_equiv {N: ℕ} {hN: ne_zero N} (k: fin N) : (fin N) ≃ (fin N) :=
{
  to_fun := @shiftk N hN (-k),
  inv_fun := @shiftk N hN (k),
  left_inv := by {
    intro x, rw shiftk, rw shiftk, dsimp, ring,
  },
  right_inv := by {
    intro x, rw shiftk, rw shiftk, dsimp, ring,
  },
}

lemma eq_412 {N: ℕ} {hN: ne_zero N} (t: (fin N) → ℂ) :
  matrix.circulant t = (Wₙ⁻¹) ⬝ (diagonal(dft t)) ⬝ Wₙ := 
begin
  apply_fun (matrix.mul Wₙ),
  rw ← matrix.mul_assoc,
  rw ← matrix.mul_assoc,
  rw inv_Wₙ, rw Wₙ_mul_iWₙ_eq_one,
  -- rw matrix.one_mul,

  funext j k,
  rw matrix.mul_mul_apply,
  rw dot_product_mul_vec, simp only,
  rw Wₙ_symmetric, rw matrix.mul_apply,
  conv_lhs {
    apply_congr, skip,
    rw circulant_apply,
  },
  rw dot_product,
  
  conv_rhs {
    apply_congr, skip,
     
    rw vec_mul_diagonal,
    -- rw pi.smul_apply,
    -- rw pi.smul_apply,
    rw matrix.one_apply,
    -- rw smul_mul_assoc,
    -- rw smul_mul_assoc,
    rw ite_mul,
    rw ite_mul,
    rw zero_mul,
    rw zero_mul, rw one_mul,
    rw mul_comm,
  },
  rw sum_ite,
  simp only [sum_const_zero, add_zero],
  rw filter_eq,
  simp only [mem_univ, if_true, sum_singleton],
  rw dft, dsimp,
  rw twiddle_comm',
  rw mul_sum,
  conv_rhs {
    apply_congr, skip,
    rw ← mul_assoc,
    rw @twiddle_sum N hN j k x,
  },

  -- rw Wₙ,simp only, dsimp,
  rw ← equiv.sum_comp (@shiftk_equiv N hN (-k)),
  rw shiftk_equiv, dsimp,  
  rw shiftk, simp only [neg_neg, add_sub_cancel],
  conv_lhs {
    apply_congr, skip, rw add_comm,
  }, 

  -- exact hN,
  assumption',
  -- extract_goal,
    rintros x a h,
  replace hinj := congr_arg (iWₙ).mul h,
  rw ← matrix.mul_assoc at hinj,
  rw ← matrix.mul_assoc at hinj,
  rw iWₙ_mul_Wₙ_eq_one at hinj,
  -- rw matrix.smul_mul at hinj,
  -- rw matrix.smul_mul at hinj,
  rw matrix.one_mul at hinj,
  rw matrix.one_mul at hinj, exact hinj,

  -- funext k n,
  -- have hz := (matrix.ext_iff.2 hinj) k n,
  -- repeat {rw pi.smul_apply at hz},
  -- have hNz : (N:ℂ) ≠ 0, {
  --   rw nat.cast_ne_zero, exact ne_zero_iff.1 hN,
  -- },
  -- rw ← sub_eq_zero at hz,
  -- rw ← smul_sub at hz,
  -- rw smul_eq_zero_iff_eq' hNz at hz,
  -- rwa sub_eq_zero at hz,
  exact hN,
end

lemma dft_idft {N: ℕ} {hN: ne_zero N} (x: (fin N) → ℂ):
  idft(dft(x)) = x := 
begin
  rw eq_406, rw eq_407,
  rw mul_vec_mul_vec,
  rw inv_Wₙ,rw iWₙ_mul_Wₙ_eq_one,
  rw one_mul_vec,
  assumption',
end

lemma idft_dft {N: ℕ} {hN: ne_zero N} (X: (fin N) → ℂ):
  dft(idft(X)) = X := 
begin
  rw eq_406, rw eq_407,
  rw mul_vec_mul_vec,
  rw inv_Wₙ, rw Wₙ_mul_iWₙ_eq_one,
  rw one_mul_vec,
  assumption',
end

lemma notice_between_411_412 {N: ℕ} 
  {hN: ne_zero N}:
  let Wrow : (fin N) → ℂ  := λ(k: fin N), exp(-2*π*I*k/N) in
  (Wₙ: matrix (fin N) (fin N) ℂ) = 
    vandermonde (Wrow) := 
begin
  dsimp,
  unfold vandermonde,
  funext k n,
  rw Wₙ, simp only,
  
  repeat {rw neg_mul,}, rw neg_div, rw neg_div,
  rw exp_neg, rw ← exp_nat_mul, rw mul_neg,
  rw exp_neg, 
  
  rw inv_eq_iff_eq_inv, rw inv_inv,
  
  rw exp_eq_exp_iff_exists_int,
  use 0,
  set η := 2*↑π*I, 
  simp only [coe_coe, algebra_map.coe_zero, 
    zero_mul, add_zero], ring,
end

end dft_matrices

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