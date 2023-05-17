import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.pos_def
import linear_algebra.matrix.spectrum
import data.complex.basic

variables {m n p : Type*}
variables [fintype m] [fintype n] [fintype p]
variables [decidable_eq m] [decidable_eq n] [decidable_eq p]

open matrix
open_locale matrix big_operators


lemma is_unit_of_pos_def {A : matrix m m ℂ} (hA: matrix.pos_def A): 
  is_unit A.det := 
begin
  rw is_unit_iff_ne_zero,
  apply ne.symm,
  cases hA with hAH hpos,
  rw is_hermitian.det_eq_prod_eigenvalues hAH,
  norm_cast,
  rw ← ne.def,
  apply ne_of_lt,
  apply finset.prod_pos,
  intros i _,
  rw hAH.eigenvalues_eq,
  apply hpos _ (λ h, _),
  have h_det : (hAH.eigenvector_matrix)ᵀ.det = 0,
    from matrix.det_eq_zero_of_row_eq_zero i (λ j, congr_fun h j),
  simpa only [h_det, not_is_unit_zero] using
    is_unit_det_of_invertible hAH.eigenvector_matrixᵀ,
end

noncomputable lemma invertible_of_pos_def {A : matrix m m ℂ} {hA: matrix.pos_def A}:
  invertible A := 
begin  
  apply invertible_of_is_unit_det,
  apply is_unit_of_pos_def,
  exact hA,
end

lemma A_add_B_P_Bt_pos_if_A_pos_B_pos 
  (P : matrix m m ℂ) (R : matrix n n ℂ) (B : matrix n m ℂ)
  -- [invertible P] [invertible R]
  (hP: matrix.pos_def P) (hR: matrix.pos_def R) :
  matrix.pos_def (B⬝P⬝Bᴴ + R) := 
begin
  cases hP with hPH hP_pos,
  cases hR with hRH hR_pos,

  split,
  -- (B ⬝ P ⬝ Bᴴ + R).is_hermitian
  unfold is_hermitian at *, rw conj_transpose_add,
  rw conj_transpose_mul,
  rw conj_transpose_mul, rw conj_transpose_conj_transpose,
  rw [hPH, hRH], rw ← matrix.mul_assoc,

  rintros x hx, simp only [is_R_or_C.re_to_complex],
  -- 0 < ⇑is_R_or_C.re (star x ⬝ᵥ (B ⬝ P ⬝ Bᴴ + R).mul_vec x)
  rw add_mul_vec,
  rw ← mul_vec_mul_vec,
  rw dot_product_add,
  rw complex.add_re,
  replace hR_pos := hR_pos x hx, 
  rw is_R_or_C.re_to_complex at hR_pos,

  replace hP_pos := hP_pos (Bᴴ.mul_vec x), 
  rw is_R_or_C.re_to_complex at hP_pos,

  rw dot_product_mul_vec,
  nth_rewrite 0  ← transpose_transpose B,
  rw ← vec_mul_mul_vec Bᵀ P (star x),
  have : star(Bᴴ.mul_vec x) = Bᵀ.mul_vec (star x), {
    rw star_mul_vec, rw conj_transpose_conj_transpose,
    funext k, rw mul_vec, rw vec_mul, dsimp, rw dot_product,
    rw dot_product, conv_rhs {
      apply_congr, skip, rw transpose_apply, rw mul_comm,
    },
  }, rw ← this, rw ← dot_product_mul_vec,
  
  by_cases hBHx: (Bᴴ.mul_vec x = 0 ), {
    rw hBHx, rw mul_vec_zero, rw dot_product_zero,
    simp only [complex.zero_re, zero_add],
    exact hR_pos,
  }, {
    exact add_pos (hP_pos hBHx) hR_pos,
  },
end

lemma right_mul_inj_of_invertible (P : matrix m m ℂ) [invertible P] :
  function.injective (λ (x : matrix n m ℂ), x ⬝ P) := 
begin
  rintros x a hax, 
  replace hax := congr_arg (λ (x : matrix n m ℂ), x ⬝ P⁻¹) hax,
  dsimp at hax, 
  rw mul_nonsing_inv_cancel_right at hax,
  rw mul_nonsing_inv_cancel_right at hax, exact hax,
  apply is_unit_det_of_invertible,
  apply is_unit_det_of_invertible,
end

lemma left_mul_inj_of_invertible (P : matrix m m ℂ) [invertible P] :
  function.injective (λ (x : matrix m n ℂ), P ⬝ x) := 
begin
  rintros x a hax, 
  replace hax := congr_arg (λ (x : matrix m n ℂ), P⁻¹ ⬝ x) hax,
  dsimp at hax, 
  rw nonsing_inv_mul_cancel_left at hax,
  rw nonsing_inv_mul_cancel_left at hax,
  exact hax,
  apply is_unit_det_of_invertible,
  apply is_unit_det_of_invertible,
end

lemma unit_matrix_sandwich
(u: n → ℂ)(v: n → ℂ)(s: ℂ)(sm: matrix unit unit ℂ) (h: s = (sm punit.star punit.star)):
  (col u ⬝ sm ⬝ row v)  = s • (col u ⬝ row v) :=
begin
  funext m k,
  rw mul_apply, rw fintype.univ_punit, rw finset.sum_singleton, rw row_apply, 
  rw mul_apply, rw fintype.univ_punit, rw finset.sum_singleton, rw col_apply,
  rw ← h,
  rw pi.smul_apply,
  rw pi.smul_apply, simp only [algebra.id.smul_eq_mul], rw mul_apply, 
  rw fintype.univ_punit, rw finset.sum_singleton, rw row_apply, rw col_apply, 
  ring,
end

lemma row_mul_mat_mul_col (A : matrix m m ℂ) (b c : m → ℂ) :
  c ⬝ᵥ A.mul_vec b = (row c ⬝ A ⬝ col b) punit.star punit.star:= 
begin
  rw mul_apply,
  rw dot_product,
  conv_rhs {
    apply_congr, skip, rw col_apply, 
    rw mul_apply, conv {
      congr, apply_congr, skip, rw row_apply,
    }, rw finset.sum_mul,
  },
  
  conv_lhs {
    apply_congr, skip, rw mul_vec, dsimp, rw dot_product,
    rw finset.mul_sum, conv {
      apply_congr, skip, rw ← mul_assoc,
    } ,
  } ,
  apply finset.sum_comm,
end

lemma one_add_row_mul_mat_col_inv (A : matrix m m ℂ)
  (b c : m → ℂ) (habc: (1 + c ⬝ᵥ A.mul_vec b) ≠ 0):
  (1 + c ⬝ᵥ A.mul_vec b)⁻¹ =
    (1 + row c ⬝ A ⬝ col b)⁻¹ punit.star punit.star :=
begin
  -- set β := (1 + row c ⬝ A⁻¹ ⬝ col b)⁻¹ punit.star punit.star,
  set γ := 1 + c ⬝ᵥ A.mul_vec b, 
  rw ← mul_left_inj' habc, rw inv_mul_cancel habc,
  rw mul_comm, rw inv_def, rw adjugate,
  simp only [
    det_unique, punit.default_eq_star, pi.add_apply, 
    one_apply_eq, ring.inverse_eq_inv', of_apply, pi.smul_apply,
    cramer_subsingleton_apply, pi.single_eq_same, 
    algebra.id.smul_eq_mul, mul_one
  ],
  rw ← row_mul_mat_mul_col, symmetry', apply mul_inv_cancel, exact habc,
end

lemma sherman_morrison (A : matrix m m ℂ) (B : matrix n n ℂ) (U : matrix m n ℂ) (V : matrix n m ℂ) 
  {hA: is_unit A.det} {hB: is_unit B.det} {hQ: is_unit (B⁻¹ + V ⬝ A⁻¹ ⬝ U).det}:
  (A + U⬝B⬝V)⁻¹ = A⁻¹ - A⁻¹⬝U⬝(B⁻¹+V⬝A⁻¹⬝U)⁻¹⬝V ⬝ A⁻¹ := 
begin
  apply inv_eq_right_inv,
  rw matrix.add_mul,
  rw matrix.mul_sub, rw mul_nonsing_inv,
  repeat {rw matrix.mul_assoc A⁻¹ _ _},
  rw mul_nonsing_inv_cancel_left,
  set Q := (B⁻¹+V⬝A⁻¹⬝U),
  rw matrix.mul_sub,
  rw sub_add_sub_comm,
  rw matrix.mul_assoc _ Q⁻¹ _,  
  rw matrix.mul_assoc U (Q⁻¹⬝V) _,
  have : U ⬝ B ⬝ V ⬝ (A⁻¹ ⬝ (U ⬝ (Q⁻¹ ⬝ V ⬝ A⁻¹))) 
    = (U ⬝ B ⬝ V ⬝ A⁻¹ ⬝ U) ⬝ (Q⁻¹ ⬝ V ⬝ A⁻¹), {
      rw ← matrix.mul_assoc _ A⁻¹ _,
      rw ← matrix.mul_assoc _ U _,
  }, rw this, clear this,
  rw ← matrix.add_mul,
  nth_rewrite 1 ← matrix.mul_one U,
  rw ←  mul_nonsing_inv B, rw ← matrix.mul_assoc _ B _,
  repeat {rw matrix.mul_assoc (U⬝B) _ _},
  rw ← matrix.mul_add (U⬝B) _ _,
  rw matrix.mul_assoc (U⬝B),
  rw matrix.mul_assoc Q⁻¹,
  rw mul_nonsing_inv_cancel_left, simp only [add_sub_cancel],
  assumption',
end

