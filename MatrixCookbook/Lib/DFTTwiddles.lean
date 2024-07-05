/-
Copyright (c) 2024 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Matrix.PEquiv
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Discrete Fourier Transform Twiddle Factors Definitios and Proofs -/

open Matrix Real Complex
open scoped Complex Matrix

namespace MatrixCookbook

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

end MatrixCookbook
