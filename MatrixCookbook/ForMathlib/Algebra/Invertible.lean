/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import Mathlib.Algebra.Ring.Invertible
import Mathlib.GroupTheory.GroupAction.ConjAct

/-! # More lemmas about `invertible` -/


variable {G M R : Type _}

section Monoid

variable [Group G] [Monoid M] [MulDistribMulAction G M]

/-- A conjugation action preserves invertibility. -/
def invertibleGroupSmul (g : G) (x : M) [Invertible x] : Invertible (g • x)
    where
  invOf := g • ⅟ x
  invOf_mul_self := by rw [← smul_mul', invOf_mul_self, smul_one]
  mul_invOf_self := by rw [← smul_mul', mul_invOf_self, smul_one]

theorem invOf_smul {G M} [Group G] [Monoid M] [MulDistribMulAction G M] (g : G) (x : M)
    [Invertible x] [Invertible (g • x)] : ⅟ (g • x) = g • ⅟ x := by
  letI := invertibleGroupSmul g x
  convert (rfl : ⅟ (g • x) = _)

variable (x y : M)

def invertibleConj [Invertible x] [Invertible y] : Invertible (x * y * ⅟ x) :=
  invertibleGroupSmul (ConjAct.toConjAct (unitOfInvertible x)) y

theorem invOf_conj [Invertible x] [Invertible y] [Invertible (x * y * ⅟ x)] :
    ⅟ (x * y * ⅟ x) = x * ⅟ y * ⅟ x := by
  letI := invertibleConj x y
  convert (rfl : ⅟ (x * y * ⅟ x) = _)

def invertibleConj' [Invertible x] [Invertible y] : Invertible (⅟ x * y * x) :=
  invertibleGroupSmul (ConjAct.toConjAct (unitOfInvertible x)⁻¹) y

theorem invOf_conj' [Invertible x] [Invertible y] [Invertible (⅟ x * y * x)] :
    ⅟ (⅟ x * y * x) = ⅟ x * ⅟ y * x := by
  letI := invertibleConj' x y
  convert (rfl : ⅟ (⅟ x * y * x) = _)

end Monoid

section Ring

variable [Ring R] (x : R)

theorem invOf_one_add [Invertible (1 + x)] : ⅟ (1 + x) = 1 - ⅟ (1 + x) * x :=
  eq_sub_of_add_eq <| (mul_one_add _ _).symm.trans <| invOf_mul_self _

theorem invOf_one_add' [Invertible (1 + x)] : ⅟ (1 + x) = 1 - x * ⅟ (1 + x) :=
  eq_sub_of_add_eq <| (one_add_mul _ _).symm.trans <| mul_invOf_self _

theorem invOf_add_one [Invertible (x + 1)] : ⅟ (x + 1) = 1 - ⅟ (x + 1) * x :=
  eq_sub_of_add_eq' <| (mul_add_one _ _).symm.trans <| invOf_mul_self _

theorem invOf_add_one' [Invertible (x + 1)] : ⅟ (x + 1) = 1 - x * ⅟ (x + 1) :=
  eq_sub_of_add_eq' <| (add_one_mul _ _).symm.trans <| mul_invOf_self _

-- Mathlib PR: https://github.com/leanprover-community/mathlib4/pull/29477
theorem eq_of_invOf_add_eq_invOf_add_invOf {a b : R} [Invertible a] [Invertible b]
    [Invertible (a + b)] (h : ⅟(a + b) = ⅟a + ⅟b) :
    a * ⅟b * a = b * ⅟a * b := by
  have h_neg_identity : -1 = ⅟a * b + ⅟b * a := by
    have : 1 = 2 + ⅟a * b + ⅟b * a := by
      rw [← invOf_mul_self (a + b), h, add_mul, mul_add, mul_add, invOf_mul_self a,
          invOf_mul_self b, ← add_assoc, add_assoc 1 _, add_comm 1 _, add_assoc 2 _,
          add_comm 2 _, add_assoc, one_add_one_eq_two]
    apply (add_left_inj 2).mp
    conv => lhs; rw [← one_add_one_eq_two, ← add_assoc, neg_add_cancel, zero_add]
    rw [add_comm, ← add_assoc]
    exact this
  have helper {x y : R} [Invertible x] [Invertible y] (h' : -1 = ⅟x * y + ⅟y * x)
      : -(y + x) = x * ⅟y * x := by
    apply add_right_cancel
    rw [(by simp : -(y + x) + y = -x)]
    conv => rhs; rhs; rw [(by simp : y = x * ⅟x * y)]
    rw [mul_assoc, mul_assoc, ← mul_add x]
    rw [(by simp : -x = x * (-1))]
    apply (mul_right_inj_of_invertible x).mpr
    rw [add_comm]
    exact h'
  have h_a_binv_a : -(b + a) = a * ⅟b * a := helper h_neg_identity
  have h_b_ainv_b : -(a + b) = b * ⅟a * b := by
    rw [add_comm] at h_neg_identity
    exact helper h_neg_identity
  rw [← h_a_binv_a, ← h_b_ainv_b, add_comm]

end Ring
