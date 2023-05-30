/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import data.matrix.basic
import linear_algebra.matrix.nonsingular_inverse

/-! # Lemmas about Inverses in Noncommutative Division Rings -/

variables {R: Type*}[division_ring R][group R]
variables (A B C : R)

lemma eq_161 {hA: A ≠ 0}{hAadd1: A + 1 ≠ 0}: 
  (1 + A⁻¹)⁻¹ = A*(A + 1)⁻¹ := begin
  apply inv_eq_of_mul_eq_one_right,
  rw [←  mul_assoc, add_mul, inv_mul_cancel hA, one_mul, mul_inv_cancel hAadd1],
end
lemma eq_163A {hA: A ≠ 0}{hB: B ≠ 0}{hAB: (A + B) ≠ 0} : 
  (A⁻¹ + B⁻¹)⁻¹ = A*(A + B)⁻¹*B := 
begin
  apply inv_eq_of_mul_eq_one_right,
  rw [← mul_assoc, ← mul_assoc, add_mul, inv_mul_cancel hA,← inv_mul_cancel hB, 
    ← mul_add, add_comm, mul_assoc B⁻¹, mul_inv_cancel hAB, mul_one],  
end
lemma eq_163B {hA: A ≠ 0}{hB: B ≠ 0}{hAB: (A + B) ≠ 0} : 
  (A⁻¹ + B⁻¹)⁻¹ = B*(A + B)⁻¹*A := 
begin
  rw [add_comm, add_comm A], 
  apply eq_163A B A, 
  assumption', 
  rwa add_comm,
end
lemma eq_163 {hA: A ≠ 0}{hB: B ≠ 0}{hAB: (A + B) ≠ 0} : 
  (A⁻¹ + B⁻¹)⁻¹ = A*(A + B)⁻¹*B ∧ (A⁻¹ + B⁻¹)⁻¹ = B*(A + B)⁻¹*A := 
begin
  split, 
  apply (eq_163A), 
  assumption',
  apply eq_163B, 
  assumption',
end

lemma eq_159 {hA: A ≠ 0} {hCBA: 1 + C * A⁻¹ * B ≠ 0}: 
  (A + B*C)⁻¹ = A⁻¹ - A⁻¹*B*(1 + C*A⁻¹*B)⁻¹*C*A⁻¹ := 
begin
  apply inv_eq_of_mul_eq_one_right,
  rw [mul_sub, add_mul, add_mul,  mul_inv_cancel], 
  simp_rw [← mul_assoc A],
  rw [mul_inv_cancel, one_mul, add_sub_assoc, sub_add_eq_sub_sub], 
  nth_rewrite 3 ← add_zero (1:R),
  rw [add_right_inj],
  simp_rw mul_assoc _ C A⁻¹,
  rw [← mul_assoc (B*C), ← sub_mul, ← sub_mul, ← mul_assoc (B*C), 
    ← sub_add_eq_sub_sub, ← add_mul],
  nth_rewrite 1 ← mul_one B,
  rw [mul_assoc, ← mul_add, ← mul_assoc C,  mul_assoc B, mul_inv_cancel, 
    mul_one, sub_self, zero_mul],
  assumption',
end

lemma eq_164_one_side {hA: A ≠ 0} {hB: B ≠ 0} {hAB: (A + B) ≠ 0}:
   A - A*(A + B)⁻¹*A = (A⁻¹ + B⁻¹)⁻¹ :=
begin
  nth_rewrite 0 ← mul_one B,
  rw eq_159,
  rw [one_mul, mul_one, mul_sub, ← mul_assoc,← mul_assoc,← mul_assoc, mul_inv_cancel,
    sub_mul, one_mul, one_mul, sub_sub_cancel, mul_assoc, inv_mul_cancel,  mul_one],
  nth_rewrite 0 ← inv_inv B,
  rw [← mul_inv_rev, add_mul, mul_assoc, mul_inv_cancel, one_mul, mul_one, add_comm], 
  assumption',
  rw one_mul,
  by_contra' h, 
  rw [← inv_mul_cancel hA, ← mul_add, mul_eq_zero] at h,
  cases h, 
  rw inv_eq_zero at h, 
  exact hA h, 
  exact hAB h,
end
lemma eq_164  {hA: A ≠ 0} {hB: B ≠ 0} {hAB: (A + B) ≠ 0} : 
  A - A*(A + B)⁻¹*A = B - B*(A + B)⁻¹*B := 
begin
  rw [eq_164_one_side, add_comm A, eq_164_one_side B A, add_comm],
  assumption', 
  rwa add_comm,
end
lemma eq_165 {hA: A ≠ 0} {hB: B ≠ 0} : A⁻¹ + B⁻¹ = A⁻¹*(A + B)*B⁻¹ :=
begin
  rw [mul_add, add_mul, inv_mul_cancel, one_mul,mul_assoc,mul_inv_cancel,
    mul_one, add_comm],
  assumption',
end