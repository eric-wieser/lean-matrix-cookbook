import linear_algebra.matrix.pos_def
import linear_algebra.matrix.spectrum
import linear_algebra.matrix.nondegenerate
import linear_algebra.matrix.determinant
import data.complex.basic


/- # Positive Definite Matrices : Extra Lemmas -/

variables {m R: Type*}[fintype m][decidable_eq m]
variables [field R][is_R_or_C R][decidable_eq R]

open matrix
open_locale matrix big_operators

lemma det_pos{A: matrix m m R} (hA: pos_def A)  : 
 0 ≠ A.det :=
begin
  rw hA.is_hermitian.det_eq_prod_eigenvalues,
  norm_cast,
  apply finset.prod_pos,
  intros i _,
  rw hM.is_hermitian.eigenvalues_eq,
  apply hM.2 _ (λ h, _),
  have h_det : (hM.is_hermitian.eigenvector_matrix)ᵀ.det = 0,
    from matrix.det_eq_zero_of_row_eq_zero i (λ j, congr_fun h j),
  simpa only [h_det, not_is_unit_zero] using
    is_unit_det_of_invertible hM.is_hermitian.eigenvector_matrixᵀ,
end

lemma vec_mul_star_eq_transpose_mul_vec {A: matrix m m R} {x: m → R} :
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

lemma pos_def.hermitian_conj {A: matrix m m R} {B: matrix m m R}
  (hA: matrix.pos_def A) : matrix.pos_def (B⬝A⬝Bᴴ) :=
begin
  cases hA with hAH hA_pos,
  split,
  rw is_hermitian at *,
  rw conj_transpose_mul,
  rw conj_transpose_mul,
  rw conj_transpose_conj_transpose,
  rw [hAH],
  rw ← matrix.mul_assoc,

  rintros x hx,
  rw ← mul_vec_mul_vec,
  rw dot_product_mul_vec,
  nth_rewrite 0  ← transpose_transpose B,
  rw ← vec_mul_mul_vec Bᵀ A (star x),
  have : star(Bᴴ.mul_vec x) = Bᵀ.mul_vec (star x), 
  { rw star_mul_vec,
    rw conj_transpose_conj_transpose,
    exact vec_mul_star_eq_transpose_mul_vec, },
  rw ← this,
  rw ← dot_product_mul_vec,
  
  -- have hBHx : (Bᴴ.mul_vec x ≠ 0 ), 
  -- { by_contra,
  --   let za := matrix.eq_zero_of_mul_vec_eq_zero (ne_of_lt pos_def.det_pos hA)
  -- }, {
  --   exact add_pos (hP_pos hBHx) hR_pos,
  -- },
end