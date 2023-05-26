import linear_algebra.matrix.nonsingular_inverse
import data.complex.basic
import matrix_cookbook.for_mathlib.linear_algebra.matrix.adjugate
import matrix_cookbook.for_mathlib.linear_algebra.matrix.nonsing_inverse

variables {n : Type*} [fintype n] [decidable_eq n]
variables {m : Type*} [fintype m] [decidable_eq m]
variables (A B : matrix n n ℂ)

open matrix
open_locale matrix big_operators

lemma eq_159 (B : matrix n m ℂ) (C : matrix m n ℂ) :
  (A + B⬝C)⁻¹ = A⁻¹ - A⁻¹⬝B⬝(1 + C⬝A⁻¹⬝B)⁻¹⬝C⬝A⁻¹ := sorry

lemma eq_167 {hAB: is_unit (1 + B⬝A).det}: (1 + A⬝B)⁻¹⬝A = A⬝(1 + B⬝A)⁻¹ := 
begin
  rw [eq_159 1 A B, inv_one, matrix.one_mul, matrix.mul_one, matrix.mul_one,
  matrix.sub_mul, matrix.one_mul, sub_eq_iff_eq_add],
  nth_rewrite 0 ← matrix.mul_one (A ⬝ (1 + B ⬝ A)⁻¹),
  rwa [matrix.mul_assoc (A ⬝ (1 + B ⬝ A)⁻¹) _ _, ← matrix.mul_add (A ⬝ (1 + B ⬝ A)⁻¹) _ _,
    nonsing_inv_mul_cancel_right],
end

lemma eq_165a {hA: is_unit A.det} {hB: is_unit B.det} : A⁻¹ + B⁻¹ = A⁻¹⬝(A + B)⬝B⁻¹ := 
begin 
  rw [matrix.mul_add, matrix.add_mul, mul_nonsing_inv_cancel_right B _ hB, 
    nonsing_inv_mul A hA, matrix.one_mul, add_comm],
end
lemma eq_165b {hA: is_unit A.det} {hB: is_unit B.det} : A⁻¹ + B⁻¹ = B⁻¹⬝(A + B)⬝A⁻¹ := 
begin 
  rw add_comm,
  rw add_comm A,
  apply eq_165a B A,
  assumption',
end

lemma eq_164_one_side (A B : matrix n n ℂ) (hA: is_unit A.det) (hB: is_unit B.det): 
  A - A⬝(A + B)⁻¹⬝A = (B⁻¹ + A⁻¹)⁻¹ := 
begin
  haveI invB := invertible_of_is_unit_det B hB,
  nth_rewrite 0 ← matrix.mul_one B,
  rw [eq_159, matrix.one_mul, matrix.mul_one, matrix.mul_sub, mul_nonsing_inv A hA, 
    matrix.sub_mul, matrix.one_mul, sub_sub_cancel,  matrix.mul_assoc _ _ A, 
    nonsing_inv_mul_cancel_right A _ hA, matrix.mul_assoc, mul_nonsing_inv_cancel_left A _ hA],
  nth_rewrite 0 ← inv_inv_of_invertible B,
  rw [← matrix.mul_inv_rev, matrix.add_mul, matrix.one_mul, mul_nonsing_inv_cancel_right B _ hB],
end


lemma eq_164 
  {hA: is_unit A.det} {hB: is_unit B.det} 
  {hAB: is_unit (A + B).det} : 
  A - A⬝(A + B)⁻¹⬝A = B - B⬝(A + B)⁻¹⬝B :=
begin
  rw [eq_164_one_side A B hA hB, add_comm A, eq_164_one_side B A hB hA, add_comm],
end