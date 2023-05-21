import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.pos_def
import linear_algebra.matrix.spectrum
import data.complex.basic
import matrix_cookbook.for_mathlib.linear_algebra.matrix.pos_def

variables {m n p : Type*}
variables [fintype m] [fintype n] [fintype p]
variables [decidable_eq m] [decidable_eq n] [decidable_eq p]

open matrix
open_locale matrix big_operators


lemma unit_matrix_mul_row {v: n → ℂ}{sm: matrix unit unit ℂ}:
  sm ⬝ row v  =  sm () () • row v := 
begin
  funext k m,
  simp only [pi.smul_apply, mul_apply, fintype.univ_unit, 
    finset.sum_singleton, col_apply, algebra.id.smul_eq_mul],
  congr,
end

lemma col_mul_unit_matrix {v: n → ℂ}{sm: matrix unit unit ℂ}:
  col v ⬝ sm =  sm () () • col v := 
begin
  funext k m,
  simp only [pi.smul_apply, mul_apply, fintype.univ_unit, 
    finset.sum_singleton, col_apply, algebra.id.smul_eq_mul],
  rw mul_comm,
  congr,
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

