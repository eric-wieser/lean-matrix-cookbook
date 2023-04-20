import data.complex.basic
import linear_algebra.matrix.hermitian
import linear_algebra.matrix.symmetric
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.adjugate
import linear_algebra.vandermonde
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
open polynomial

lemma vec_eq_vec_iff (v w: n → R) : 
  v = w ↔ ∀ k : n, v k = w k := 
begin
  split,
  intros h k, rw h,

  intros h, ext k,
  specialize h k, exact h,
end

lemma mat_eq_mat_iff (v w: matrix m n R) : 
  v = w ↔ ∀ (j: m)(k: n), v j k = w j k:= 
begin
  split,
  rintros h i j, rw h at *,
  intro h,
  ext i j, specialize h i j, exact h,
end

-- variable {N: ℕ}
/- Are we really forced to have the DFT matrix 
noncomputable because the complex exponnetial function is 
non-computable?
-/

-- eq_403 : Twiddle Factors
noncomputable def Wkn {N: ℕ} (k n: fin N) : ℂ :=  
complex.exp(complex.I * 2 * π * k * n / N)

-- Forward DFT Matrix
noncomputable def W_N {N: ℕ}: matrix (fin N) (fin N) ℂ :=
λ (k n: fin N), Wkn k n

-- Inverse Twiddle Factors
noncomputable def iWkn {N: ℕ} (k n: fin N) : ℂ :=  
complex.exp(-complex.I * 2 * π * k * n / N)

-- Inverse DFT Matrix
noncomputable def iW_N {N: ℕ} : matrix (fin N) (fin N) ℂ :=
λ (k n: fin N), iWkn k n

-- eq_404
noncomputable def dft {N: ℕ} (x: (fin N) → ℂ) : (fin N → ℂ) := 
λ (k: fin N), ∑ (n : fin N), (Wkn k n) * (x n)

-- eq_405
noncomputable def idft {N: ℕ} (X: (fin N) → ℂ) : (fin N → ℂ) := 
λ (k: fin N), (∑ (n : fin N),  ((1/N)•iWkn) k n * (X n))

lemma eq_406 {N: ℕ} (x: fin N → ℂ) : 
dft x = matrix.mul_vec W_N x := 
begin
  rw vec_eq_vec_iff, intro k,
  rw [dft, matrix.mul_vec, dot_product],
  refl,
end

lemma eq_407 {N: ℕ} (X: fin N → ℂ) : 
idft X = (matrix.mul_vec ((1/N)•iW_N) X) := 
begin
  rw vec_eq_vec_iff, intro k,
  rw [idft, matrix.mul_vec, dot_product],
  refl,
end

lemma twiddle_comm {N: ℕ}(k n: fin N) :
  Wkn k n = Wkn n k := begin
  rw Wkn,rw Wkn, ring_nf,
end

@[simp] lemma twiddle_cancel {N:ℕ} (k n: fin N) :
  Wkn n k * iWkn k n = 1 :=
begin
  rw Wkn, rw iWkn,
  rw ← complex.exp_add, ring_nf, rw complex.exp_zero,
end

@[simp] lemma twiddle_mul {N:ℕ} (j k l: fin N) :
  Wkn j k * iWkn k l = 
    (exp(I * 2 * π * (j - l) / N)) ^ (k:ℕ) :=
begin
  rw Wkn, rw iWkn, 
  rw ← exp_add, 
  have : I * 2 * π * j * k / N + -I * 2 * π * k * l / N = 
    I * 2 * π * (j - l)*k / N, by ring, rw this, 
  set rt := I * 2 * π * (j - l), 
  have : rt * ↑k / ↑N = (rt / N) * k, by ring, rw this,
  rw mul_comm, 
  exact exp_int_mul _ _,
end

lemma W_N_symmetric {N: ℕ} :
  (W_N: matrix (fin N) (fin N) ℂ) = (W_Nᵀ) := 
begin
  rw [transpose, W_N],
  funext k n,
  simp only [of_apply, twiddle_comm],
end

lemma Wkn_dot_iWkn_diag {N:ℕ} (n: fin N) : 
  ∑ (i : fin N), ((Wkn n i) * (iWkn i n)) = N := 
begin
  simp only [twiddle_cancel,sum_const, card_fin, nat.smul_one_eq_coe],
end

lemma one_lt_N_zero_ne {N: ℕ} (hN: 1 < N) : (↑N:ℂ) ≠ (0:ℂ) := begin
  simp only [ne.def, nat.cast_eq_zero], 
  linarith,
end

lemma complex_exp_ne_one_if_kn {N:ℕ} {hN: 1 < N} 
    {k n: fin N} {h: ¬(k = n)} :
  exp (I * 2 * ↑π * (↑k - ↑n) / ↑N) ≠ 1 :=
begin
  by_contra' hE,
  rw complex.exp_eq_one_iff at hE,
  cases hE with m hE,

  have hm1 : I * 2 * ↑π * (↑k - ↑n) / ↑N = (2 * ↑π * I) * ((↑k - ↑n) / ↑N), by ring,
  have hm2 : ↑m * (2 * ↑π * I) = (2 * ↑π * I) * m, by ring,
  
  rw [hm1, hm2, mul_right_inj' two_pi_I_ne_zero] at hE, 
  rw div_eq_iff at hE,
  
  sorry,
  exact one_lt_N_zero_ne hN,
end

lemma Wkn_dot_iWKn_offdiag {N:ℕ} {hN: 1 < N} (k n: fin N) (h: ¬(k = n)) :
  ∑ (i : fin N), Wkn k i * iWkn i n = 0 := 
begin
  simp_rw [twiddle_mul],
  rw fin.sum_univ_eq_sum_range,
  rw geom_sum_eq, 
  simp only [_root_.div_eq_zero_iff],
  left,
  rw sub_eq_zero, set α := I * 2 * ↑π * (↑k - ↑n) / ↑N,
  simp_rw [← complex.exp_nat_mul, mul_comm ↑N _],
  
  rw div_mul_cancel, 
  have : I * 2 * ↑π * (↑k - ↑n) = (↑k - ↑n) * ( 2 * ↑π * I), by ring,
  rw this, 
  have : (↑k - ↑n) * ( 2 * ↑π * I) = ((↑k - ↑n):ℤ) * ( 2 * ↑π * I), 
  by { simp only [coe_coe, int.cast_sub, int.cast_coe_nat],},
  rw this,
  
  apply exp_int_mul_two_pi_mul_I, 
  exact one_lt_N_zero_ne hN,
  apply complex_exp_ne_one_if_kn , assumption',
end

lemma eq_408 {N: ℕ} {h: 1 ≤ N} : 
(W_N : matrix (fin N) (fin N) ℂ)⁻¹ = 
  (1/N)•(W_Nᴴ)ᵀ :=
-- Seems star means hermitian and not just conjugate
begin
  rw inv_eq_left_inv,
  funext k n, 
  rw matrix.mul, simp only [dot_product],
  simp only [nsmul_eq_mul, mul_eq_mul],
  
  by_cases (k = n),
  rw W_N, 
  rw [h], simp only [one_apply_eq],
  sorry,
  
end

lemma eq_409 {N: ℕ} {h: 1 ≤ N} : 
(W_N) ⬝ (iW_N) = 
  N•(1: matrix (fin N) (fin N) ℂ) := 
begin
  
  rw W_N, rw iW_N,
  by_cases hNl1: (1 < N),
    funext k n,
    by_cases (k = n),
    rw matrix.mul, simp only [dot_product],
    rw [h, Wkn_dot_iWkn_diag],  
    simp only [nat.smul_one_eq_coe, pi.smul_apply, one_apply_eq],

    -- !(k = n)
    rw matrix.mul, simp only [dot_product],
    rw Wkn_dot_iWKn_offdiag  _ _ h ,  
    rw [pi.smul_apply,pi.smul_apply, one_apply_ne h, smul_zero],
    exact hNl1,

  have hN1: 1 = N, exact eq_of_le_of_not_lt h hNl1, 
  rw matrix.mul, simp only [dot_product],
  rw ← hN1 at *,
  funext k n, fin_cases k, fin_cases n, 
  simp only [ -- Whatever this is, it is too much!!!
    fintype.univ_of_subsingleton, twiddle_mul, sub_self, mul_zero, 
    zero_div, exp_zero, one_pow, sum_const, card_singleton,
    nat.smul_one_eq_coe, nat.cast_one, one_apply_eq],
end

lemma eq_410 {N: ℕ} : 
(star W_N : matrix (fin N) (fin N) ℂ) = W_Nᴴ :=
begin
  unfold star,
end

noncomputable def W11 {N : ℕ} : ℂ := complex.exp(-complex.I * 2 * π / N)

lemma eq_411 {N: ℕ} {m: ℤ} : 
  complex.exp(-2 * π * I  / N) ^ (m + N/2: ℂ)  = 
    -complex.exp(-2 * π * I / N) ^ (m:ℂ)  := 
begin

  have hne: exp ((-2) * ↑π * I / ↑N) ^ (↑N / 2) = -1, by {
    sorry,
  },

  set α := exp(- 2 * π * I / N),
  rw complex.cpow_add,
  simp only [cpow_int_cast],
  rw ← neg_one_mul, rw mul_comm,
  rw mul_left_inj',
  apply hne,
  
  -- calc exp (↑(m + ↑N / 2) * fac) 
  --         = exp (↑m * fac + (↑N / 2) * fac) : by { 
  --           have : ↑(m + ↑N / 2) * fac = ↑m * fac + ↑N / 2 * fac, by {
  --           },
  --          }
  -- ...     = -exp fac ^ m : by { 
  --   sorry,
  -- },
  
end
lemma eq_412 : sorry := sorry

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