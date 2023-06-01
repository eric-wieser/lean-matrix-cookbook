/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import data.matrix.basic
import algebra.invertible

/-! # Lemmas about Inverses in Noncommutative Division Rings -/

variables {R: Type*}[ring R]
variables (A B C U V : R)

lemma ring_inv_eq_of_mul_eq_one_right {hA: is_unit A}: 
  A * B = 1 → ring.inverse A = B := begin
  intro h,
  apply_fun (λ x, A * x),
  simp only,
  rw [ring.mul_inverse_cancel,  eq_comm],
  assumption',
  apply (is_unit.is_regular hA).left, 
end

lemma is_unit_of_ring_inverse_mul_eq_one: 
  ring.inverse A*B = 1 → is_unit A := begin
  nontriviality R,
  contrapose,
  intro h,
  rw [ring.inverse_non_unit A h, zero_mul, ← ne.def, ne_comm],
  exact one_ne_zero,
end

lemma ring_inv_eq_of_mul_eq_one_right' {hA: is_unit A}: 
  A * B = 1 → ring.inverse A = B := begin
  intro hAB,
  apply_fun (λ x, A * x),
  simp only,
  rw [ring.mul_inverse_cancel,  eq_comm],
  assumption',
  apply (is_unit.is_regular hA).left,
end

lemma ring_inverse_inverse {hA: is_unit A}: 
  ring.inverse (ring.inverse A) = A := begin
  apply ring_inv_eq_of_mul_eq_one_right,
  simp only [is_unit_ring_inverse, hA],
  rw [ring.inverse_mul_cancel], 
  exact hA,
end

lemma is_unit_add_is_unit_add_inverses {hA: is_unit A} {hB: is_unit B}{hAB: is_unit (A + B)} : 
  is_unit (ring.inverse A + ring.inverse B) := begin
  have hA' : is_unit A,{assumption',}, 
  have hB' : is_unit B,{assumption',},
  cases hA with a hA',
  cases hB with b hB', 
  let hiA := hA',
  let hiB := hB',
  apply_fun ring.inverse at hiA, rw ← hiA,
  apply_fun ring.inverse at hiB, rw ← hiB,
  refine (units.is_unit_units_mul a _).1 _,
  refine (units.is_unit_mul_units _ b).1 _,
  rwa [mul_add, add_mul, ring.inverse_mul_cancel_right, ring.mul_inverse_cancel, one_mul, 
    hA', hB', add_comm],
  rwa hA',
  rwa hB',
end

lemma is_unit_one_add_ring_inverse {hA : is_unit A} {hAadd1 : is_unit (A + 1)}:
  is_unit(1 + ring.inverse A) := begin
  rw ← ring.inverse_one,
  apply is_unit_add_is_unit_add_inverses,
  exact is_unit_one,
  exact hA, rwa add_comm,
end

lemma sherman_morrison 
  {hA: is_unit A} {hB: is_unit B} {hABUV: is_unit (A + U * B * V)}
    {hQ: is_unit (ring.inverse B + V * ring.inverse A * U)}:
  ring.inverse(A + U*B*V) = ring.inverse A - (ring.inverse A) * U * 
    ring.inverse(ring.inverse B+V* ring.inverse A* U)* V * (ring.inverse A) := 
begin
  apply ring_inv_eq_of_mul_eq_one_right,
  rotate,
  rw add_mul, rw mul_sub,rw ring.mul_inverse_cancel,
  set iA := (ring.inverse A),
  set iQ := ring.inverse(ring.inverse B + V * iA * U),
  rw [mul_assoc iA, mul_assoc iA, mul_assoc iA, mul_assoc _ _ V,
    ring.mul_inverse_cancel_left, mul_sub, sub_add_sub_comm, mul_assoc U _ iA,
    ← mul_assoc _ _ (iQ * V * iA), ← mul_assoc _ _ (iQ * V * iA), ← add_mul],
  nth_rewrite 1 ← mul_one U,
  rw [←ring.mul_inverse_cancel B,← mul_assoc _ B _, mul_assoc (U*B), mul_assoc (U*B), ← mul_add,
    mul_assoc (U*B), mul_assoc iQ, ← mul_assoc V, ring.mul_inverse_cancel_left, add_sub_cancel],
  assumption',
end

lemma eq_161b {hA : is_unit A} {hAadd1 : is_unit (A + 1)}:
  ring.inverse (1 + ring.inverse A) = A* (ring.inverse (A + 1)) :=
begin
  have hAiv: is_unit(1 + ring.inverse A), 
  {  apply is_unit_one_add_ring_inverse, 
    assumption', },
  apply_fun (λ x, ( 1 + ring.inverse A) * x),
  simp only,
  rw [ring.mul_inverse_cancel ( 1 + ring.inverse A),
    ← mul_assoc, add_mul, ring.inverse_mul_cancel, one_mul, ring.mul_inverse_cancel],
  assumption', 
  apply (is_unit.is_regular hAiv).left,
end

lemma eq_163A {hA: is_unit A}{hB: is_unit B}{hAB: is_unit (A + B)}: 
  ring.inverse(ring.inverse A + ring.inverse B) = A*ring.inverse(A + B)*B := 
begin
  have : is_unit (ring.inverse A + ring.inverse B),
  { apply is_unit_add_is_unit_add_inverses, assumption',},
  rw ring_inv_eq_of_mul_eq_one_right, rotate,
  rw [← mul_assoc, ← mul_assoc, add_mul, ring.inverse_mul_cancel, ← ring.inverse_mul_cancel B, 
    ← mul_add, add_comm, mul_assoc (ring.inverse B), ring.mul_inverse_cancel, mul_one],  
  assumption',
end

lemma eq_163B {hA: is_unit A}{hB: is_unit B}{hAB: is_unit (A + B)}:
  ring.inverse (ring.inverse A + ring.inverse B) = B*ring.inverse (A + B)*A := 
begin
   have : is_unit (ring.inverse A + ring.inverse B),
  { apply is_unit_add_is_unit_add_inverses, assumption',},
  rw [add_comm, add_comm A], 
  apply eq_163A B A, 
  assumption',
  rwa add_comm, 
end
lemma eq_163 {hA: is_unit A}{hB: is_unit B}{hAB: is_unit (A + B)}:
  ring.inverse(ring.inverse A + ring.inverse B) = A*ring.inverse(A + B)*B  ∧
  ring.inverse (ring.inverse A + ring.inverse B) = B*ring.inverse (A + B)*A := 
begin
   have : is_unit (ring.inverse A + ring.inverse B),
  { apply is_unit_add_is_unit_add_inverses, assumption',},
  split, 
  apply (eq_163A), 
  assumption',
  apply eq_163B, 
  assumption',
end

lemma eq_159 {hA: is_unit A} {hABC: is_unit (1 + C*(ring.inverse A)*B)}{hABC: is_unit (A + B * C)}: 
    ring.inverse(A + B*C) = ring.inverse A - (ring.inverse A)*B*
      ring.inverse(1 + C*(ring.inverse A)*B)*C*(ring.inverse A) := 
begin
  apply ring_inv_eq_of_mul_eq_one_right, rotate,
  rw [mul_sub, add_mul, add_mul,  ring.mul_inverse_cancel], 
  simp_rw [← mul_assoc A],
  rw [ring.mul_inverse_cancel, one_mul, add_sub_assoc, sub_add_eq_sub_sub], 
  nth_rewrite 3 ← add_zero (1:R),
  rw [add_right_inj],
  simp_rw mul_assoc _ C (ring.inverse A),
  rw [← mul_assoc (B*C), ← sub_mul, ← sub_mul, ← mul_assoc (B*C), 
    ← sub_add_eq_sub_sub, ← add_mul],
  nth_rewrite 1 ← mul_one B,
  rw [mul_assoc, ← mul_add, ← mul_assoc C,  mul_assoc B, ring.mul_inverse_cancel, 
    mul_one, sub_self, zero_mul],
  assumption',
end

lemma eq_164_one_side {hA: is_unit A}{hB: is_unit B}{hAB: is_unit (A + B)}
  {hiAB: is_unit (1 + ring.inverse A * B)} {hiAiB: is_unit (ring.inverse A + ring.inverse B)}:
   A - A*ring.inverse (A + B)*A = ring.inverse(ring.inverse A + ring.inverse B) :=
begin
  nth_rewrite 0 ← mul_one B,
  rw [eq_159, one_mul, mul_one, mul_sub, ← mul_assoc,← mul_assoc,← mul_assoc, 
    ring.mul_inverse_cancel, sub_mul, one_mul, one_mul, sub_sub_cancel, mul_assoc,
    ring.inverse_mul_cancel, mul_one, eq_comm, ring_inv_eq_of_mul_eq_one_right],
  assumption,
  rw [add_mul, ring.inverse_mul_cancel_left, ← mul_assoc],
  nth_rewrite 1 ← one_mul (ring.inverse (1 + ring.inverse A * B)),
  rw [← add_mul, add_comm, ring.mul_inverse_cancel],
  assumption', 
  rwa one_mul, 
  rwa mul_one,
end
lemma eq_164 {hA: is_unit A}{hB: is_unit B}{hAB: is_unit (A + B)}
  {hiAB: is_unit (1 + ring.inverse A * B)} {hAiB: is_unit (1 + ring.inverse B * A)} 
  {hiAiB: is_unit (ring.inverse A + ring.inverse B)}: 
  A - A*ring.inverse(A + B)*A = B - B*ring.inverse(A + B)*B := 
begin
  rw [eq_164_one_side, add_comm A, eq_164_one_side B A, add_comm],
  assumption',
  rwa add_comm,
  rwa add_comm,
end
lemma eq_165 {hA: is_unit A}{hB: is_unit B}: 
  ring.inverse A + ring.inverse B = ring.inverse A*(A + B)* ring.inverse B :=
begin
  rw [mul_add, add_mul, ring.inverse_mul_cancel, one_mul, mul_assoc, ring.mul_inverse_cancel,
    mul_one, add_comm],
  assumption',
end