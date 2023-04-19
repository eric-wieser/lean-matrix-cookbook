import data.complex.basic
import linear_algebra.matrix.hermitian
import linear_algebra.matrix.symmetric
import linear_algebra.matrix.nonsingular_inverse
import data.complex.exponential
import analysis.special_functions.trigonometric.basic
import data.matrix.basic

open_locale real matrix big_operators
open matrix
open equiv equiv.perm finset
open complex
open polynomial

lemma one_lt_N_zero_ne {N: ℕ} (hN: 1 < N) : (↑N:ℂ) ≠ (0:ℂ) := begin
  simp only [ne.def, nat.cast_eq_zero], 
  linarith,
end

lemma complex_exp_neg_one {N: ℕ} {hN: 1 < N}: 
  exp ((-2) * ↑π * I / ↑N) ^ (↑N / 2: ℂ) = -1 := 
begin
  set α := exp(- 2 * π * I / N),
  have hα : α ≠ 0, by {apply exp_ne_zero,}, 
  have hxy := cpow_def_of_ne_zero (hα) (N/2: ℂ),
  -- norm_cast at *,
  rw hxy,   -- Error Here
  change α with exp(- 2 * π * I / N),
  rw log_exp,
  -- ring_exp,
  have : ((-2) * ↑π * I / ↑N * (↑N / 2)) = -(2*π*I)/2, by {
    rw neg_mul, rw neg_mul,
    ring_nf, rw mul_inv_cancel (one_lt_N_zero_ne hN), rw one_mul,
  },
  rw this, 
  have : -(2 * ↑π * I) / 2 = -↑π * I, by { ring}, rw this,
  rw neg_mul, rw exp_neg, rw exp_pi_mul_I, ring,
  sorry,
  sorry,
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
