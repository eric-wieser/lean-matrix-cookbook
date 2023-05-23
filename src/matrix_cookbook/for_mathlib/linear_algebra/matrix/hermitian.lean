/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import linear_algebra.matrix.hermitian
import data.complex.basic

/-! # Hermitian Matrices : Extra Lemmas -/

namespace matrix

variables {R : Type*} 
variables {n : Type*}[fintype n][decidable_eq n]

open_locale matrix

variables [field R][is_R_or_C R]

lemma is_hermitian.star_weighted_inner_product
  {A : matrix n n R} {v w : n → R} (hA : A.is_hermitian) :
  star (star w ⬝ᵥ A.mul_vec v) = star v ⬝ᵥ A.mul_vec w :=
begin
  rw ← star_star (A.mul_vec v),
  rw star_mul_vec, 
  rw hA.eq,
  rw star_dot_product_star, 
  rw star_star,
  rw ← dot_product_mul_vec,
end

lemma weighted_inner_product_comm {A : matrix n n R} {v w : n → R} (hA: is_hermitian A):
  is_R_or_C.re (star v ⬝ᵥ A.mul_vec w) = is_R_or_C.re (star w ⬝ᵥ A.mul_vec v) :=
begin
  rw ← is_hermitian.star_weighted_inner_product hA,
  nth_rewrite 0 ← is_R_or_C.conj_re,
  rw star_ring_end_apply, 
  rw star_star,
end

end matrix

