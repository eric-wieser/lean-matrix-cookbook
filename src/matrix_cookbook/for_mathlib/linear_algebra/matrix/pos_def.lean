/-
Copyright (c) 2023 Mohanad Ahmed. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mohanad Ahmed
-/

import linear_algebra.matrix.pos_def
import linear_algebra.matrix.spectrum
import linear_algebra.matrix.nondegenerate
import linear_algebra.matrix.determinant
import data.complex.basic

/-! # Positive Definite Matrices : Extra Lemmas -/

variables {m n: Type*}
variables [fintype m][decidable_eq m][fintype n][decidable_eq n]
variables {R: Type*}[field R][is_R_or_C R][decidable_eq R]

open matrix
open complex
open_locale matrix big_operators
open_locale complex_order

lemma pos_def.det_ne_zero{A: matrix m m R} (hA: pos_def A)  : 
  A.det ≠ 0 :=
  -- 0 < A.det := 
begin
  rw hA.is_hermitian.det_eq_prod_eigenvalues,
  symmetry',
  norm_cast, 
  apply ne_of_lt,
  apply finset.prod_pos,
  intros i _,
  rw hA.is_hermitian.eigenvalues_eq,
  apply hA.2 _ (λ h, _),
  have h_det : (hA.is_hermitian.eigenvector_matrix)ᵀ.det = 0,
    from matrix.det_eq_zero_of_row_eq_zero i (λ j, congr_fun h j),
  simpa only [h_det, not_is_unit_zero] using
    is_unit_det_of_invertible hA.is_hermitian.eigenvector_matrixᵀ,
end

lemma vec_mul_star_eq_transpose_mul_vec {A: matrix m n R} {x: m → R} :
  vec_mul (star x) A = Aᵀ.mul_vec (star x) :=
begin
  funext k,
  rw mul_vec,
  rw vec_mul,
  dsimp,
  rw dot_product,
  rw dot_product,
  conv_rhs
  { apply_congr,
    skip,
    rw transpose_apply,
    rw mul_comm, },
end

lemma star_conj_transpose_mul_vec  {A: matrix m n R} {x: m → R}:
  star(Aᴴ.mul_vec x) = Aᵀ.mul_vec (star x) :=
begin
  rw star_mul_vec,
  rw conj_transpose_conj_transpose,
  exact vec_mul_star_eq_transpose_mul_vec,
end

lemma pos_def.hermitian_conj_is_semidef {A: matrix m m R} {B: matrix n m R}
  (hA: matrix.pos_def A) : matrix.pos_semidef (B⬝A⬝Bᴴ) :=
begin
  cases hA with hAH hA_pos,
  split,
  rw is_hermitian at *, 
  rw [conj_transpose_mul, conj_transpose_mul, conj_transpose_conj_transpose, 
      hAH, ← matrix.mul_assoc],

  intros x,
  rw [← mul_vec_mul_vec, dot_product_mul_vec],
  nth_rewrite 0  ← transpose_transpose B,
  rw [← vec_mul_mul_vec Bᵀ A (star x),  ← star_conj_transpose_mul_vec, 
   ← dot_product_mul_vec ],
  
  by_cases h: (Bᴴ.mul_vec x ≠ 0), 
  { exact le_of_lt ((hA_pos (Bᴴ.mul_vec x)) h), },
  { push_neg at h, 
    rw h, 
    simp only [mul_vec_zero, star_zero, zero_dot_product, is_R_or_C.zero_re'], },
end

lemma pos_def.add_semidef {A: matrix m m R} {B: matrix m m R}
  (hA: matrix.pos_def A) (hB: matrix.pos_semidef B) : matrix.pos_def (A + B) :=
begin
  split,
  exact is_hermitian.add hA.is_hermitian hB.1,
  
  rintros x hx,
  rw add_mul_vec,
  rw dot_product_add,
  rw map_add,
  
  exact add_pos_of_pos_of_nonneg (hA.2 x hx) (hB.2 x),
end

