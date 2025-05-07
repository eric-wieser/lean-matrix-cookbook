import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Fintype.BigOperators
-- import Mathlib.Tactic.NormFin

/-! # Missing lemmas about Trace and Determinant of 4 x 4 matrices -/


variable {R m n p : Type*}

open scoped Matrix BigOperators

namespace Matrix

section NonUnitalNonAssocSemiring
variable [NonUnitalNonAssocSemiring R]

open RightActions

theorem mul_single_eq [Fintype m] [DecidableEq m] [DecidableEq p]
    (A : Matrix n m R) (i : m) (j : p) (r : R) :
    A * single i j r = updateCol 0 j (A.col i <• r) := by
  ext i' j'
  obtain rfl | hj := eq_or_ne j' j
  · rw [mul_single_apply_same, updateCol_self, Pi.smul_apply, col_apply, op_smul_eq_mul]
  · rw [mul_single_apply_of_ne _ _ _ _ _ hj, updateCol_ne hj, zero_apply]

theorem single_mul_eq [Fintype n] [DecidableEq n] [DecidableEq p]
    (i : p) (j : n) (r : R)  (A : Matrix n m R) :
    single i j r * A = updateRow 0 i (r • A.row j) := by
  ext i' j'
  obtain rfl | hj := eq_or_ne i' i
  · rw [single_mul_apply_same, updateRow_self, Pi.smul_apply, row_apply, smul_eq_mul]
  · rw [single_mul_apply_of_ne _ _ _ _ _ hj, updateRow_ne hj, zero_apply]

end NonUnitalNonAssocSemiring

variable [CommRing R]

theorem one_fin_four :
    (1 : Matrix (Fin 4) (Fin 4) R) = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem trace_fin_four {A : Matrix (Fin 4) (Fin 4) R} : A.trace = A 0 0 + A 1 1 + A 2 2 + A 3 3 :=
  Fin.sum_univ_four _

theorem det_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    A.det =
      A 0 0 * A 1 1 * A 2 2 * A 3 3 - A 0 0 * A 1 1 * A 2 3 * A 3 2 -
                                                  A 0 0 * A 1 2 * A 2 1 * A 3 3 +
                                                A 0 0 * A 1 2 * A 2 3 * A 3 1 +
                                              A 0 0 * A 1 3 * A 2 1 * A 3 2 -
                                            A 0 0 * A 1 3 * A 2 2 * A 3 1 -
                                          A 0 1 * A 1 0 * A 2 2 * A 3 3 +
                                        A 0 1 * A 1 0 * A 2 3 * A 3 2 +
                                      A 0 1 * A 1 2 * A 2 0 * A 3 3 -
                                    A 0 1 * A 1 2 * A 2 3 * A 3 0 -
                                  A 0 1 * A 1 3 * A 2 0 * A 3 2 +
                                A 0 1 * A 1 3 * A 2 2 * A 3 0 +
                              A 0 2 * A 1 0 * A 2 1 * A 3 3 -
                            A 0 2 * A 1 0 * A 2 3 * A 3 1 -
                          A 0 2 * A 1 1 * A 2 0 * A 3 3 +
                        A 0 2 * A 1 1 * A 2 3 * A 3 0 +
                      A 0 2 * A 1 3 * A 2 0 * A 3 1 -
                    A 0 2 * A 1 3 * A 2 1 * A 3 0 -
                  A 0 3 * A 1 0 * A 2 1 * A 3 2 +
                A 0 3 * A 1 0 * A 2 2 * A 3 1 +
              A 0 3 * A 1 1 * A 2 0 * A 3 2 -
            A 0 3 * A 1 1 * A 2 2 * A 3 0 -
          A 0 3 * A 1 2 * A 2 0 * A 3 1 +
        A 0 3 * A 1 2 * A 2 1 * A 3 0 := by
  rw [Matrix.det_succ_row_zero]
  simp_rw [det_fin_three, submatrix_apply, Fin.sum_univ_four]
  -- `norm_fin` can't handle these
  have h10 : (1 : Fin 4).succAbove 0 = 0 := rfl
  have h11 : (1 : Fin 4).succAbove 1 = 2 := rfl
  have h12 : (1 : Fin 4).succAbove 2 = 3 := rfl
  have h20 : (2 : Fin 4).succAbove 0 = 0 := rfl
  have h21 : (2 : Fin 4).succAbove 1 = 1 := rfl
  have h22 : (2 : Fin 4).succAbove 2 = 3 := rfl
  have h30 : (3 : Fin 4).succAbove 0 = 0 := rfl
  have h31 : (3 : Fin 4).succAbove 1 = 1 := rfl
  have h32 : (3 : Fin 4).succAbove 2 = 2 := rfl
  simp_rw [h10, h11, h12, h20, h21, h22, h30, h31, h32, Fin.zero_succAbove]
  -- `norm_fin` is too slow here
  have s0 : (0 : Fin 3).succ = 1 := rfl
  have s1 : (1 : Fin 3).succ = 2 := rfl
  have s2 : (2 : Fin 3).succ = 3 := rfl
  simp_rw [s0, s1, s2]
  -- `norm_num` is too slow here
  have a0 : (-1 : R) ^ ((0 : Fin 4) : ℕ) = 1 := Even.neg_one_pow (by decide)
  have a1 : (-1 : R) ^ ((1 : Fin 4) : ℕ) = -1 := Odd.neg_one_pow (by decide)
  have a2 : (-1 : R) ^ ((2 : Fin 4) : ℕ) = 1 := Even.neg_one_pow (by decide)
  have a3 : (-1 : R) ^ ((3 : Fin 4) : ℕ) = -1 := Odd.neg_one_pow (by decide)
  simp_rw [a0, a1, a2, a3]
  ring

end Matrix
