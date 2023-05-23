/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.pos_def
import linear_algebra.matrix.spectrum
import data.complex.basic
import matrix_cookbook.for_mathlib.linear_algebra.matrix.pos_def

/-! # Sherman Morrison (sometimes called Woodbury Identity) and other support Lemmas -/

variables {m n p : Type*}
variables [fintype m] [fintype n] [fintype p]
variables [decidable_eq m] [decidable_eq n] [decidable_eq p]

open matrix
open_locale matrix big_operators


lemma unit_matrix_mul_row {v: n → ℂ}{sm: matrix unit unit ℂ}:
  sm ⬝ row v  =  sm () () • row v := 
begin
  funext k m,
  simp only [pi.smul_apply, mul_apply, fintype.univ_unit, 
    finset.sum_singleton, col_apply, algebra.id.smul_eq_mul],
  congr,
end

lemma col_mul_unit_matrix {v: n → ℂ}{sm: matrix unit unit ℂ}:
  col v ⬝ sm =  sm () () • col v := 
begin
  funext k m,
  simp only [pi.smul_apply, mul_apply, fintype.univ_unit, 
    finset.sum_singleton, col_apply, algebra.id.smul_eq_mul],
  rw mul_comm,
  congr,
end

lemma unit_matrix_sandwich
(u: n → ℂ)(v: n → ℂ)(s: ℂ)(sm: matrix unit unit ℂ) (h: s = (sm punit.star punit.star)):
  (col u ⬝ sm ⬝ row v)  = s • (col u ⬝ row v) :=
begin
  rw col_mul_unit_matrix,
  rw ←  matrix.smul_mul, 
  rw h,
end

lemma row_mul_mat_mul_col (A : matrix m m ℂ) (b c : m → ℂ) :
  c ⬝ᵥ A.mul_vec b = (row c ⬝ A ⬝ col b) () ():= 
begin
  rw [mul_apply, dot_product], 
  conv_rhs 
  { apply_congr, 
    skip, 
    rw [col_apply, mul_apply], 
    conv 
    { congr, 
      apply_congr, 
      skip, 
      rw row_apply, }, 
    rw finset.sum_mul, },
  
  conv_lhs 
  { apply_congr, 
    skip, 
    rw mul_vec, 
    dsimp, 
    rw [dot_product, finset.mul_sum], 
    conv 
    { apply_congr, 
      skip, 
      rw ← mul_assoc, } , } ,
  apply finset.sum_comm,
end

lemma one_add_row_mul_mat_col_inv (A : matrix m m ℂ)
  (b c : m → ℂ) (habc: (1 + c ⬝ᵥ A.mul_vec b) ≠ 0):
  (1 + c ⬝ᵥ A.mul_vec b)⁻¹ =
    (1 + row c ⬝ A ⬝ col b)⁻¹ punit.star punit.star :=
begin
  set γ := 1 + c ⬝ᵥ A.mul_vec b, 
  rw [← mul_left_inj' habc, inv_mul_cancel habc, mul_comm, inv_def, adjugate],
  simp only [
    det_unique, punit.default_eq_star, pi.add_apply, 
    one_apply_eq, ring.inverse_eq_inv', of_apply, pi.smul_apply,
    cramer_subsingleton_apply, pi.single_eq_same, 
    algebra.id.smul_eq_mul, mul_one
  ],
  rw ← row_mul_mat_mul_col, 
  symmetry', 
  exact mul_inv_cancel habc, 
end

lemma sherman_morrison (A : matrix m m ℂ) (B : matrix n n ℂ) (U : matrix m n ℂ) (V : matrix n m ℂ) 
  {hA: is_unit A.det} {hB: is_unit B.det} {hQ: is_unit (B⁻¹ + V ⬝ A⁻¹ ⬝ U).det}:
  (A + U⬝B⬝V)⁻¹ = A⁻¹ - A⁻¹⬝U⬝(B⁻¹+V⬝A⁻¹⬝U)⁻¹⬝V ⬝ A⁻¹ := 
begin
  rw inv_eq_right_inv,
  rw [matrix.add_mul, matrix.mul_sub, mul_nonsing_inv],
  repeat {rw matrix.mul_assoc A⁻¹ _ _},
  set Q := (B⁻¹+V⬝A⁻¹⬝U),
  rw [mul_nonsing_inv_cancel_left, matrix.mul_sub, sub_add_sub_comm, 
    matrix.mul_assoc _ Q⁻¹ _,  matrix.mul_assoc U (Q⁻¹⬝V) _],

  have : U ⬝ B ⬝ V ⬝ (A⁻¹ ⬝ (U ⬝ (Q⁻¹ ⬝ V ⬝ A⁻¹))) 
    = (U ⬝ B ⬝ V ⬝ A⁻¹ ⬝ U) ⬝ (Q⁻¹ ⬝ V ⬝ A⁻¹), 
  { rw ← matrix.mul_assoc _ A⁻¹ _,
    rw ← matrix.mul_assoc _ U _, }, 
  rw this,
  rw ← matrix.add_mul,
  nth_rewrite 1 ← matrix.mul_one U,
  rw [←  mul_nonsing_inv B, ← matrix.mul_assoc _ B _],
  repeat {rw matrix.mul_assoc (U⬝B) _ _},
  rw [← matrix.mul_add (U⬝B) _ _, matrix.mul_assoc (U⬝B), matrix.mul_assoc Q⁻¹,
    mul_nonsing_inv_cancel_left, add_sub_cancel], 
  assumption',
end

