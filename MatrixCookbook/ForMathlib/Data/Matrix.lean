module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Data.Fintype.BigOperators

/-! # Missing lemmas about Trace and Determinant of 4 x 4 matrices -/

@[expose] public section

variable {R m n p : Type*}

open scoped Matrix BigOperators

namespace Matrix

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
  rw [det_succ_row_zero]
  simp [det_fin_three, Fin.sum_univ_succ, Fin.succAbove, pow_succ]
  ring

end Matrix
