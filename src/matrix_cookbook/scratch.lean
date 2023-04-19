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

section dft_matrices

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

end dft_matrices