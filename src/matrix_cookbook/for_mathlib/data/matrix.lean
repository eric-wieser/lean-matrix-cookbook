import linear_algebra.matrix.trace
import linear_algebra.matrix.determinant
import data.matrix.notation
import data.fintype.big_operators
import tactic.norm_fin

/-! # Missing lemmas about Trace and Determinant of 4 x 4 matrices -/

variables {R : Type*}[field R]

open_locale matrix big_operators
open matrix

lemma trace_fin_four {A : matrix (fin 4) (fin 4) R} :
  A.trace = A 0 0 + A 1 1 + A 2 2 + A 3 3 := 
begin
  rw matrix.trace,  
  rw fin.sum_univ_four, 
  repeat {rw diag,},
end

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
  -- There is no way but to brute force this. "Sophisticated" tactics are too slow!!
  have s0: fin.succ (0: fin 3) = 1, {norm_fin,},
  have s1: fin.succ (1: fin 3) = 2, {norm_fin,},
  have s2: fin.succ (2: fin 3) = 3, {norm_fin,},
  have a0 : ((-1:R)^(↑(0: fin 4))) = (1:R), {rw fin.coe_zero,rw pow_zero,},
  have a1 : (-1:R)^(↑(1: fin 4)) = -1, {rw fin.coe_one,rw pow_one,},
  have a2 : (-1:R)^(↑(2: fin 4)) = 1, 
  { rw neg_one_pow_eq_pow_mod_two, 
    rw fin.coe_two, 
    rw nat.mod_self, 
    rw pow_zero, },
  have a3 : (-1:R)^(↑(3: fin 4)) = -1,
  { rw neg_one_pow_eq_pow_mod_two, 
    have : ↑(3: fin 4) = (3:ℕ), {refl,}, 
    rw this, 
    have : 3 % 2  = 1, by refl, 
    rw this, 
    rw pow_one, },
  
  rw matrix.det_succ_row_zero, 
  conv_lhs 
  { apply_congr,
    skip,
    rw det_fin_three, }, 
  rw fin.sum_univ_four, 
  repeat {rw submatrix_apply}, 
  rw [a0, a1, a2, a3], 
  repeat {rw fin.one_succ_above_zero},
  repeat {rw fin.zero_succ_above},
  rw [s0, s1, s2],
  rw fin.one_succ_above_one,
  have : (1: fin 4).succ_above 2 = 3, {refl,},  rw this,
  have : (2: fin 4).succ_above 0 = 0, {refl,},  rw this,
  have : (2: fin 4).succ_above 1 = 1, {refl,},  rw this,
  have : (2: fin 4).succ_above 2 = 3, {refl,},  rw this,
  have : (3: fin 4).succ_above 0 = 0, {refl,},  rw this,
  have : (3: fin 4).succ_above 1 = 1, {refl,},  rw this,
  have : (3: fin 4).succ_above 2 = 2, {refl,},  rw this,
  ring,
end