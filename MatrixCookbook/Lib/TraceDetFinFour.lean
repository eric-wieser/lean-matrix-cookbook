/-
Copyright (c) 2023 Mohanad Ahmed, Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed, Eric Wieser
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
-- import Mathlib.Tactic.NormFin
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.CharP.Basic
import MatrixCookbook.ForMathlib.Data.Matrix

/-!
# Traces and Determinants of 1st, 2nd and 3rd Powers of 4x4 Matrices

This file contains lemmas in rather verbose form of matrix fin 4 fin 4 R.

These are used to prove equation 27 in the matrix cookbook.

The results are all for commutative rings.

It's not clear that these results belong in mathlib as lemmas; they might be better suited to
tactic support in `norm_num`.
-/


open scoped Matrix BigOperators

open Matrix

variable {R : Type _} [CommRing R]

theorem trace_pow_two_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    trace (A ^ 2) =
      A 0 0 ^ 2 + A 1 1 ^ 2 + A 2 2 ^ 2 + A 3 3 ^ 2 + 2 * A 0 1 * A 1 0 + 2 * A 0 2 * A 2 0 +
              2 * A 0 3 * A 3 0 +
            2 * A 1 2 * A 2 1 +
          2 * A 1 3 * A 3 1 +
        2 * A 2 3 * A 3 2 := by
  simp_rw [Matrix.trace_fin_four, pow_two, mul_apply, Fin.sum_univ_four]
  ring

-- porting note: added
set_option linter.unreachableTactic false in
theorem trace_pow_three_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    trace (A ^ 3) =
      A 0 0 * (A 0 0 ^ 2 + A 0 1 * A 1 0 + A 0 2 * A 2 0 + A 0 3 * A 3 0) +
                                    A 1 1 *
                                      (A 1 1 ^ 2 + A 0 1 * A 1 0 + A 1 2 * A 2 1 + A 1 3 * A 3 1) +
                                  A 2 2 *
                                    (A 2 2 ^ 2 + A 0 2 * A 2 0 + A 1 2 * A 2 1 + A 2 3 * A 3 2) +
                                A 3 3 *
                                  (A 3 3 ^ 2 + A 0 3 * A 3 0 + A 1 3 * A 3 1 + A 2 3 * A 3 2) +
                              A 1 0 *
                                (A 0 0 * A 0 1 + A 0 1 * A 1 1 + A 0 2 * A 2 1 + A 0 3 * A 3 1) +
                            A 2 0 *
                              (A 0 0 * A 0 2 + A 0 1 * A 1 2 + A 0 2 * A 2 2 + A 0 3 * A 3 2) +
                          A 0 1 * (A 0 0 * A 1 0 + A 1 0 * A 1 1 + A 1 2 * A 2 0 + A 1 3 * A 3 0) +
                        A 3 0 * (A 0 0 * A 0 3 + A 0 1 * A 1 3 + A 0 2 * A 2 3 + A 0 3 * A 3 3) +
                      A 2 1 * (A 0 2 * A 1 0 + A 1 1 * A 1 2 + A 1 2 * A 2 2 + A 1 3 * A 3 2) +
                    A 0 2 * (A 0 0 * A 2 0 + A 1 0 * A 2 1 + A 2 0 * A 2 2 + A 2 3 * A 3 0) +
                  A 3 1 * (A 0 3 * A 1 0 + A 1 1 * A 1 3 + A 1 2 * A 2 3 + A 1 3 * A 3 3) +
                A 1 2 * (A 0 1 * A 2 0 + A 1 1 * A 2 1 + A 2 1 * A 2 2 + A 2 3 * A 3 1) +
              A 0 3 * (A 0 0 * A 3 0 + A 1 0 * A 3 1 + A 2 0 * A 3 2 + A 3 0 * A 3 3) +
            A 3 2 * (A 0 3 * A 2 0 + A 1 3 * A 2 1 + A 2 2 * A 2 3 + A 2 3 * A 3 3) +
          A 1 3 * (A 0 1 * A 3 0 + A 1 1 * A 3 1 + A 2 1 * A 3 2 + A 3 1 * A 3 3) +
        A 2 3 * (A 0 2 * A 3 0 + A 1 2 * A 3 1 + A 2 2 * A 3 2 + A 3 2 * A 3 3) := by
  simp_rw [Matrix.trace_fin_four, pow_three, mul_apply, Fin.sum_univ_four]
  ring

theorem det_one_add_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    (1 + A).det =
      A 0 0 + A 1 1 + A 2 2 + A 3 3 + A 0 0 * A 1 1 - A 0 1 * A 1 0 + A 0 0 * A 2 2 -
                                                                                                                          A
                                                                                                                              0
                                                                                                                              2 *
                                                                                                                            A
                                                                                                                              2
                                                                                                                              0 +
                                                                                                                        A
                                                                                                                            0
                                                                                                                            0 *
                                                                                                                          A
                                                                                                                            3
                                                                                                                            3 -
                                                                                                                      A
                                                                                                                          0
                                                                                                                          3 *
                                                                                                                        A
                                                                                                                          3
                                                                                                                          0 +
                                                                                                                    A
                                                                                                                        1
                                                                                                                        1 *
                                                                                                                      A
                                                                                                                        2
                                                                                                                        2 -
                                                                                                                  A
                                                                                                                      1
                                                                                                                      2 *
                                                                                                                    A
                                                                                                                      2
                                                                                                                      1 +
                                                                                                                A
                                                                                                                    1
                                                                                                                    1 *
                                                                                                                  A
                                                                                                                    3
                                                                                                                    3 -
                                                                                                              A
                                                                                                                  1
                                                                                                                  3 *
                                                                                                                A
                                                                                                                  3
                                                                                                                  1 +
                                                                                                            A
                                                                                                                2
                                                                                                                2 *
                                                                                                              A
                                                                                                                3
                                                                                                                3 -
                                                                                                          A
                                                                                                              2
                                                                                                              3 *
                                                                                                            A
                                                                                                              3
                                                                                                              2 +
                                                                                                        A
                                                                                                              0
                                                                                                              0 *
                                                                                                            A
                                                                                                              1
                                                                                                              1 *
                                                                                                          A
                                                                                                            2
                                                                                                            2 -
                                                                                                      A
                                                                                                            0
                                                                                                            0 *
                                                                                                          A
                                                                                                            1
                                                                                                            2 *
                                                                                                        A
                                                                                                          2
                                                                                                          1 -
                                                                                                    A
                                                                                                          0
                                                                                                          1 *
                                                                                                        A
                                                                                                          1
                                                                                                          0 *
                                                                                                      A
                                                                                                        2
                                                                                                        2 +
                                                                                                  A
                                                                                                        0
                                                                                                        1 *
                                                                                                      A
                                                                                                        1
                                                                                                        2 *
                                                                                                    A
                                                                                                      2
                                                                                                      0 +
                                                                                                A 0
                                                                                                      2 *
                                                                                                    A
                                                                                                      1
                                                                                                      0 *
                                                                                                  A
                                                                                                    2
                                                                                                    1 -
                                                                                              A 0
                                                                                                    2 *
                                                                                                  A
                                                                                                    1
                                                                                                    1 *
                                                                                                A 2
                                                                                                  0 +
                                                                                            A 0 0 *
                                                                                                A 1
                                                                                                  1 *
                                                                                              A 3
                                                                                                3 -
                                                                                          A 0 0 *
                                                                                              A 1
                                                                                                3 *
                                                                                            A 3 1 -
                                                                                        A 0 1 *
                                                                                            A 1 0 *
                                                                                          A 3 3 +
                                                                                      A 0 1 *
                                                                                          A 1 3 *
                                                                                        A 3 0 +
                                                                                    A 0 3 * A 1 0 *
                                                                                      A 3 1 -
                                                                                  A 0 3 * A 1 1 *
                                                                                    A 3 0 +
                                                                                A 0 0 * A 2 2 *
                                                                                  A 3 3 -
                                                                              A 0 0 * A 2 3 *
                                                                                A 3 2 -
                                                                            A 0 2 * A 2 0 * A 3 3 +
                                                                          A 0 2 * A 2 3 * A 3 0 +
                                                                        A 0 3 * A 2 0 * A 3 2 -
                                                                      A 0 3 * A 2 2 * A 3 0 +
                                                                    A 1 1 * A 2 2 * A 3 3 -
                                                                  A 1 1 * A 2 3 * A 3 2 -
                                                                A 1 2 * A 2 1 * A 3 3 +
                                                              A 1 2 * A 2 3 * A 3 1 +
                                                            A 1 3 * A 2 1 * A 3 2 -
                                                          A 1 3 * A 2 2 * A 3 1 +
                                                        A 0 0 * A 1 1 * A 2 2 * A 3 3 -
                                                      A 0 0 * A 1 1 * A 2 3 * A 3 2 -
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
          A 0 3 * A 1 2 * A 2 1 * A 3 0 +
        1 := by
  simp only [det_fin_four, Matrix.add_apply, one_apply_eq]
  simp (disch := decide) only [one_apply_ne]
  ring

theorem sq_trace_fin_four (A : Matrix (Fin 4) (Fin 4) R) :
    trace A ^ 2 =
      A 0 0 ^ 2 + A 1 1 ^ 2 + A 2 2 ^ 2 + A 3 3 ^ 2 + 2 * A 0 0 * A 1 1 + 2 * A 0 0 * A 2 2 +
              2 * A 0 0 * A 3 3 +
            2 * A 1 1 * A 2 2 +
          2 * A 1 1 * A 3 3 +
        2 * A 2 2 * A 3 3 := by
  rw [trace_fin_four, pow_two]
  ring
