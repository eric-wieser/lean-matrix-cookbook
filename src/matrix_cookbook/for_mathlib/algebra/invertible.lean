/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import algebra.invertible
import group_theory.group_action.conj_act

variables {G M R : Type*}

/-! # More lemmas about `invertible` -/

section monoid
variables [group G] [monoid M] [mul_distrib_mul_action G M]

/-- x conjugation action preserves invertibility. -/
def invertible_group_smul (g : G) (x : M)
  [invertible x] : 
  invertible (g • x) :=
{ inv_of := g • ⅟x, 
  inv_of_mul_self := by rw [←smul_mul', inv_of_mul_self, smul_one],
  mul_inv_of_self := by rw [←smul_mul', mul_inv_of_self, smul_one] }

lemma inv_of_smul {G M} [group G] [monoid M] [mul_distrib_mul_action G M] (g : G) (x : M)
  [invertible x] [invertible (g • x)] : 
  ⅟(g • x) = g • ⅟x :=
begin
  letI := invertible_group_smul g x,
  convert (rfl : ⅟(g • x) = _),
end

variables (x y : M)

def invertible_conj [invertible x] [invertible y] : invertible (x*y*⅟x) :=
invertible_group_smul (conj_act.to_conj_act (unit_of_invertible x)) y

lemma inv_of_conj [invertible x] [invertible y] [invertible (x*y*⅟x)] : 
  ⅟(x*y*⅟x) = x*⅟y*⅟x :=
begin
  letI := invertible_conj x y,
  convert (rfl : ⅟(x*y*⅟x) = _),
end

def invertible_conj' [invertible x] [invertible y] : invertible (⅟x*y*x) :=
invertible_group_smul (conj_act.to_conj_act (unit_of_invertible x)⁻¹) y

lemma inv_of_conj' [invertible x] [invertible y] [invertible (⅟x*y*x)] : 
  ⅟(⅟x*y*x) = ⅟x*⅟y*x :=
begin
  letI := invertible_conj' x y,
  convert (rfl : ⅟(⅟x*y*x) = _),
end

end monoid

section ring
variables [ring R] (x : R)

lemma inv_of_one_add [invertible (1 + x)] : ⅟(1 + x) = 1 - ⅟(1 + x) * x :=
eq_sub_of_add_eq $ (mul_one_add _ _).symm.trans $ inv_of_mul_self _

lemma inv_of_one_add' [invertible (1 + x)] : ⅟(1 + x) = 1 - x * ⅟(1 + x) :=
eq_sub_of_add_eq $ (one_add_mul _ _).symm.trans $ mul_inv_of_self _

lemma inv_of_add_one [invertible (x + 1)] : ⅟(x + 1) = 1 - ⅟(x + 1) * x :=
eq_sub_of_add_eq' $ (mul_add_one _ _).symm.trans $ inv_of_mul_self _

lemma inv_of_add_one' [invertible (x + 1)] : ⅟(x + 1) = 1 - x * ⅟(x + 1) :=
eq_sub_of_add_eq' $ (add_one_mul _ _).symm.trans $ mul_inv_of_self _

end ring