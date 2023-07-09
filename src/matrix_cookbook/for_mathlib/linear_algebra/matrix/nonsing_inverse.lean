/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import linear_algebra.matrix.nonsingular_inverse

/-! # Missing lemmas about injectivity of invertible matrix multipliciations -/

variables {m: Type*}[fintype m][decidable_eq m]
variables {n: Type*}[fintype n][decidable_eq n]
variables {R: Type*}[comm_ring R]

open matrix
open_locale matrix big_operators

lemma matrix.right_mul_inj_of_invertible (P : matrix m m R) [invertible P] :
  function.injective (λ (x : matrix n m R), x ⬝ P) := 
begin
  -- This chain does not work since we get * while we need ⬝ 
  -- have w:= is_unit.mul_left_injective (
  --   (is_unit_iff_is_unit_det P).2 (is_unit_det_of_invertible P)
  -- ),

  let hdetP_unit := matrix.is_unit_det_of_invertible P,
  rintros x a hax, 
  replace hax := congr_arg (λ (x : matrix n m R), x ⬝ P⁻¹) hax,
  dsimp at hax, 
  simp only [mul_inv_cancel_right_of_invertible] at hax,
  exact hax,
end

lemma matrix.left_mul_inj_of_invertible (P : matrix m m R) [invertible P] :
  function.injective (λ (x : matrix m n R), P ⬝ x) := 
begin
  let hdetP_unit := matrix.is_unit_det_of_invertible P,
  rintros x a hax, 
  replace hax := congr_arg (λ (x : matrix m n R), P⁻¹ ⬝ x) hax,
  simp only [inv_mul_cancel_left_of_invertible] at hax,
  exact hax,
end

lemma matrix.left_mul_inj_of_is_unit_det {P : matrix m m R} (hdetP_unit: is_unit P.det) :
  function.injective (λ (x : matrix m n R), P ⬝ x) := 
begin
  haveI invP := invertible_of_is_unit_det P hdetP_unit,
  apply matrix.left_mul_inj_of_invertible,
end

lemma matrix.right_mul_inj_of_is_unit_det {P : matrix m m R} (hdetP_unit: is_unit P.det) :
  function.injective (λ (x : matrix n m R), x ⬝ P) := 
begin
  haveI invP := invertible_of_is_unit_det P hdetP_unit,
  apply matrix.right_mul_inj_of_invertible,
end
