/-
Copyright (c) 2023 Mohanad Ahmed, Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed, Eric Wieser
-/

import linear_algebra.matrix.trace
import linear_algebra.matrix.determinant
import data.matrix.notation
import data.fintype.big_operators
import tactic.norm_fin

/-! # Missing lemmas about Trace and Determinant of 4 x 4 matrices -/

variables {R : Type*} [comm_ring R]

open_locale matrix big_operators
namespace matrix

lemma one_fin_four :
  (1 : matrix (fin 4) (fin 4) R) = !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] :=
by { ext i j, fin_cases i; fin_cases j; refl }

lemma trace_fin_four {A : matrix (fin 4) (fin 4) R} :
  A.trace = A 0 0 + A 1 1 + A 2 2 + A 3 3 :=
fin.sum_univ_four _

lemma det_fin_four (A : matrix (fin 4) (fin 4) R) :
  A.det =
    A 0 0*A 1 1*A 2 2*A 3 3 - A 0 0*A 1 1*A 2 3*A 3 2 - A 0 0*A 1 2*A 2 1*A 3 3 +
    A 0 0*A 1 2*A 2 3*A 3 1 + A 0 0*A 1 3*A 2 1*A 3 2 - A 0 0*A 1 3*A 2 2*A 3 1 -
    A 0 1*A 1 0*A 2 2*A 3 3 + A 0 1*A 1 0*A 2 3*A 3 2 + A 0 1*A 1 2*A 2 0*A 3 3 -
    A 0 1*A 1 2*A 2 3*A 3 0 - A 0 1*A 1 3*A 2 0*A 3 2 + A 0 1*A 1 3*A 2 2*A 3 0 +
    A 0 2*A 1 0*A 2 1*A 3 3 - A 0 2*A 1 0*A 2 3*A 3 1 - A 0 2*A 1 1*A 2 0*A 3 3 +
    A 0 2*A 1 1*A 2 3*A 3 0 + A 0 2*A 1 3*A 2 0*A 3 1 - A 0 2*A 1 3*A 2 1*A 3 0 -
    A 0 3*A 1 0*A 2 1*A 3 2 + A 0 3*A 1 0*A 2 2*A 3 1 + A 0 3*A 1 1*A 2 0*A 3 2 -
    A 0 3*A 1 1*A 2 2*A 3 0 - A 0 3*A 1 2*A 2 0*A 3 1 + A 0 3*A 1 2*A 2 1*A 3 0 :=
begin
  rw matrix.det_succ_row_zero,
  simp_rw [det_fin_three, submatrix_apply, fin.sum_univ_four],
  -- `norm_fin` can't handle these
  have h10 : (1 : fin 4).succ_above 0 = 0 := rfl,
  have h11 : (1 : fin 4).succ_above 1 = 2 := rfl,
  have h12 : (1 : fin 4).succ_above 2 = 3 := rfl,
  have h20 : (2 : fin 4).succ_above 0 = 0 := rfl,
  have h21 : (2 : fin 4).succ_above 1 = 1 := rfl,
  have h22 : (2 : fin 4).succ_above 2 = 3 := rfl,
  have h30 : (3 : fin 4).succ_above 0 = 0 := rfl,
  have h31 : (3 : fin 4).succ_above 1 = 1 := rfl,
  have h32 : (3 : fin 4).succ_above 2 = 2 := rfl,
  simp_rw [h10, h11, h12, h20, h21, h22, h30, h31, h32, fin.zero_succ_above],
  -- `norm_fin` is too slow here
  have s0 : (0 : fin 3).succ = 1 := rfl,
  have s1 : (1 : fin 3).succ = 2 := rfl,
  have s2 : (2 : fin 3).succ = 3 := rfl,
  simp_rw [s0, s1, s2],
  -- `norm_num` is too slow here
  have a0 : (-1 : R)^((0 : fin 4) : ℕ) = 1 := even.neg_one_pow dec_trivial,
  have a1 : (-1 : R)^((1 : fin 4) : ℕ) = -1 := odd.neg_one_pow dec_trivial,
  have a2 : (-1 : R)^((2 : fin 4) : ℕ) = 1 := even.neg_one_pow dec_trivial,
  have a3 : (-1 : R)^((3 : fin 4) : ℕ) = -1 := odd.neg_one_pow dec_trivial,
  simp_rw [a0, a1, a2, a3],
  ring
end

end matrix
