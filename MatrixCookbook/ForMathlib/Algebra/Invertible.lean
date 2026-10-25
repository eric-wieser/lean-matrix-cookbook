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

end Ring
