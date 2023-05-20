import linear_algebra.matrix.nonsingular_inverse
import data.complex.basic
import matrix_cookbook.mat_inv_lib
import matrix_cookbook.for_mathlib.linear_algebra.matrix.nonsing_inverse
import matrix_cookbook.for_mathlib.linear_algebra.matrix.pos_def

/-! # Inverses -/

namespace matrix_cookbook
variables {m n p : Type*}
variables [fintype m] [fintype n] [fintype p]
variables [decidable_eq m] [decidable_eq n] [decidable_eq p]
variables (A B C : matrix n n ℂ)
open matrix
open_locale matrix big_operators


/-! ## Basic -/

/-! ### Definition -/

lemma eq_145 (h : is_unit A.det) : A * A⁻¹ = 1 ∧ A⁻¹ * A = 1 :=
⟨mul_nonsing_inv _ h, nonsing_inv_mul _ h⟩

/-! ### Cofactors and Adjoint -/

lemma eq_146 (n : ℕ) (A : matrix (fin n.succ) (fin n.succ) ℂ) (i j) :
  adjugate A j i = (-1)^(i + j : ℕ) * det (A.submatrix i.succ_above j.succ_above) := sorry
lemma eq_147 : (adjugate A)ᵀ = of (λ i j, adjugate A j i) := rfl
lemma eq_148 : adjugate A = (adjugate A)ᵀᵀ := rfl

/-! ### Determinant -/

/-- Note: adapted from column 0 to column 1. -/
lemma eq_149 (n : ℕ) (A : matrix (fin n.succ) (fin n.succ) ℂ) :
  det A = ∑ i : fin n.succ, (-1) ^ (i : ℕ) * A i 0 * det (A.submatrix i.succ_above fin.succ) :=
det_succ_column_zero _
lemma eq_150 : sorry := sorry

/-! ### Construction -/

lemma eq_151 : A⁻¹ = (1/A.det) • adjugate A :=
by rw [inv_def, ring.inverse_eq_inv, one_div]

/-! ### Condition number -/

lemma eq_152 : sorry := sorry
lemma eq_153 : sorry := sorry
lemma eq_154 : sorry := sorry

/-! ## Exact Relations -/

/-! ### Basic -/

lemma eq_155 (A B : matrix m m ℂ) : (A * B)⁻¹ = B⁻¹ * A⁻¹ := mul_inv_rev _ _

/-! ### The Woodbury identity -/

lemma eq_156 (A : matrix m m ℂ) (B : matrix n n ℂ) (C : matrix m n ℂ)
  {hA: is_unit A.det} {hB: is_unit B.det} {hQ: is_unit (B⁻¹ + Cᵀ ⬝ A⁻¹ ⬝ C).det}: 
  (A + C⬝B⬝Cᵀ)⁻¹ = A⁻¹ - A⁻¹⬝C⬝(B⁻¹+Cᵀ⬝A⁻¹⬝C)⁻¹⬝Cᵀ ⬝ A⁻¹ :=  
begin
  apply sherman_morrison,
  assumption',
end

lemma eq_156_hermitianized (A : matrix m m ℂ) (B : matrix n n ℂ) (C : matrix m n ℂ)
  {hA: is_unit A.det} {hB: is_unit B.det} {hQ: is_unit (B⁻¹ + Cᴴ ⬝ A⁻¹ ⬝ C).det}: 
  (A + C⬝B⬝Cᴴ)⁻¹ = A⁻¹ - A⁻¹⬝C⬝(B⁻¹+Cᴴ⬝A⁻¹⬝C)⁻¹⬝Cᴴ ⬝ A⁻¹ :=  
begin
  apply sherman_morrison,
  assumption',
end

lemma eq_157 (A : matrix m m ℂ) (B : matrix n n ℂ) (U : matrix m n ℂ) (V : matrix n m ℂ) 
  {hA: is_unit A.det} {hB: is_unit B.det} {hQ: is_unit (B⁻¹ + V ⬝ A⁻¹ ⬝ U).det}:
  (A + U⬝B⬝V)⁻¹ = A⁻¹ - A⁻¹⬝U⬝(B⁻¹+V⬝A⁻¹⬝U)⁻¹⬝V ⬝ A⁻¹ := 
begin
  apply sherman_morrison,
  assumption',
end

lemma eq_158_hermitianized (P : matrix m m ℂ) (R : matrix n n ℂ) (B : matrix n m ℂ)
  [invertible P] [invertible R]
  {hP: matrix.pos_def P} {hR: matrix.pos_def R} : 
  (P⁻¹ + Bᴴ⬝R⁻¹⬝B)⁻¹⬝Bᴴ⬝R⁻¹ = P⬝Bᴴ⬝(B⬝P⬝Bᴴ + R)⁻¹ := 
begin
  -- This is equation 80:
  -- http://www.stat.columbia.edu/~liam/teaching/neurostat-spr12/papers/hmm/KF-welling-notes.pdf

  have hP_unit := is_unit_iff_ne_zero.2 (pos_def.det_ne_zero hP),
  have hR_unit := is_unit_iff_ne_zero.2 (pos_def.det_ne_zero hR),
  have hP_inv_unit := is_unit_nonsing_inv_det P hP_unit,
  have hR_inv_unit := is_unit_nonsing_inv_det R hR_unit,
  have hComb_unit: is_unit (R + B ⬝ P ⬝ Bᴴ).det, 
  { apply is_unit_iff_ne_zero.2, 
    apply pos_def.det_ne_zero,
    apply pos_def.add_semidef hR,
    apply pos_def.hermitian_conj_is_semidef hP,
    assumption', },
  have : is_unit (R⁻¹⁻¹ + Bᴴᴴ ⬝ P⁻¹⁻¹ ⬝ Bᴴ).det, 
  { simp only [inv_inv_of_invertible, conj_transpose_conj_transpose],
    apply hComb_unit, },

  rw add_comm _ R,
  nth_rewrite 1 ← conj_transpose_conj_transpose B,
  rw eq_156_hermitianized P⁻¹ R⁻¹ Bᴴ,
  simp only [inv_inv_of_invertible, conj_transpose_conj_transpose],
  rw [matrix.sub_mul,  matrix.sub_mul], 
  rw sub_eq_iff_eq_add,
  apply_fun (matrix.mul P⁻¹), 
  rw matrix.mul_add,
  repeat {rw ←  matrix.mul_assoc P⁻¹ _ _}, 
  apply_fun (λ x, x⬝R),  dsimp,
  rw matrix.add_mul,
  simp only [inv_mul_of_invertible, matrix.one_mul, 
    inv_mul_cancel_right_of_invertible],
  repeat {rw matrix.mul_assoc (Bᴴ⬝(R + B ⬝ P ⬝ Bᴴ)⁻¹)},
  rw ← matrix.mul_add (Bᴴ⬝(R + B ⬝ P ⬝ Bᴴ)⁻¹), 
  rw nonsing_inv_mul_cancel_right,

  assumption',

  apply right_mul_inj_of_invertible,
  apply left_mul_inj_of_invertible,
end

/-! ### The Kailath Variant -/

lemma eq_159 (A : matrix m m ℂ) (B : matrix m n ℂ) (C : matrix n m ℂ)
  {hA: is_unit A.det} {h: is_unit (1 + C ⬝ A⁻¹ ⬝ B).det} :
  (A + B⬝C)⁻¹ = A⁻¹ - A⁻¹⬝B⬝(1 + C⬝A⁻¹⬝B)⁻¹⬝C⬝A⁻¹ :=
begin
  nth_rewrite 0 ← matrix.mul_one B,
  rw eq_157 A 1 B C,
  simp only [inv_one], assumption',
  simp only [det_one, is_unit_one],
  rw inv_one, 
  assumption',
end

/-! ### Sherman-Morrison -/

lemma eq_160 (A : matrix m m ℂ) (b c : m → ℂ) 
  [invertible A](habc: (1 + c ⬝ᵥ A⁻¹.mul_vec b) ≠ 0):
  (A + col b ⬝ row c)⁻¹ = A⁻¹ - (1 + c ⬝ᵥ (A⁻¹.mul_vec b))⁻¹ • (A⁻¹⬝(col b ⬝ row c)⬝A⁻¹) :=
begin
  let hA := is_unit_det_of_invertible A,

  rw eq_159, simp only [sub_right_inj],
  apply_fun (λ x, x⬝A),  
  dsimp, 
  rw nonsing_inv_mul_cancel_right,
  rw ← matrix.smul_mul, 
  rw nonsing_inv_mul_cancel_right,
  apply_fun (λ x, A⬝x),  
  dsimp, rw ← matrix.mul_smul,
  repeat {rw matrix.mul_assoc A⁻¹},
  rw mul_nonsing_inv_cancel_left,
  rw mul_nonsing_inv_cancel_left,
  
  rw unit_matrix_sandwich,
  apply one_add_row_mul_mat_col_inv, 
  
  assumption',

  apply left_mul_inj_of_invertible,
  apply right_mul_inj_of_invertible,
  simp only [det_unique, punit.default_eq_star, dmatrix.add_apply, one_apply_eq],
  rw ←row_mul_mat_mul_col, 
  apply is_unit_iff_ne_zero.2 habc, 
end

/-! ### The Searle Set of Identities -/

lemma eq_161 : (1 + A⁻¹)⁻¹ = A⬝(A + 1)⁻¹ := sorry
lemma eq_162 : (A + Bᵀ⬝B)⁻¹⬝B = A⁻¹⬝B⬝(1 + Bᵀ⬝A⁻¹⬝B)⁻¹:= sorry
lemma eq_163 : (A⁻¹ + B⁻¹)⁻¹ = A⬝(A + B)⁻¹⬝B ∧ (A⁻¹ + B⁻¹)⁻¹ = B⬝(A + B)⁻¹⬝A := sorry
lemma eq_164 : A - A⬝(A + B)⁻¹⬝A = B - B⬝(A + B)⁻¹⬝B := sorry
lemma eq_165 : A⁻¹ + B⁻¹ = A⁻¹⬝(A + B)⁻¹⬝B⁻¹ := sorry
lemma eq_166 : (1 + A⬝B)⁻¹ = 1 - A⬝(1 + B⬝A)⁻¹⬝B := sorry
lemma eq_167 : (1 + A⬝B)⁻¹⬝A = A⬝(1 + B⬝A)⁻¹ := sorry

/-! ### Rank-1 update of inverse of inner product -/

/-! ### Rank-1 update of Moore-Penrose Inverse -/

lemma eq_168 : sorry := sorry
lemma eq_169 : sorry := sorry
lemma eq_170 : sorry := sorry
lemma eq_171 : sorry := sorry
lemma eq_172 : sorry := sorry
lemma eq_173 : sorry := sorry
lemma eq_174 : sorry := sorry
lemma eq_175 : sorry := sorry
lemma eq_176 : sorry := sorry
lemma eq_177 : sorry := sorry
lemma eq_178 : sorry := sorry
lemma eq_179 : sorry := sorry
lemma eq_180 : sorry := sorry
lemma eq_181 : sorry := sorry
lemma eq_182 : sorry := sorry
lemma eq_183 : sorry := sorry

/-! ## Implication on Inverses -/

lemma eq_184 : (A + B)⁻¹ = A⁻¹ + B⁻¹ → A⬝B⁻¹⬝A = B⬝A⁻¹⬝B := sorry

/-! ### A PosDef identity -/

lemma eq_185 : sorry := sorry

/-! ## Approximations -/

lemma eq_186 : sorry := sorry
lemma eq_187 : sorry := sorry
lemma eq_188 : sorry := sorry
lemma eq_189 : sorry := sorry
lemma eq_190 : sorry := sorry
lemma eq_191 : sorry := sorry
lemma eq_192 : sorry := sorry
lemma eq_193 : sorry := sorry
lemma eq_194 : sorry := sorry
lemma eq_195 : sorry := sorry
lemma eq_196 : sorry := sorry
lemma eq_197 : sorry := sorry

/-! ## Generalized Inverse -/

lemma eq_198 : sorry := sorry

/-! ### Definition -/

/-! ## Pseudo Inverse -/

lemma eq_199 : sorry := sorry
lemma eq_200 : sorry := sorry
lemma eq_201 : sorry := sorry
lemma eq_202 : sorry := sorry
lemma eq_203 : sorry := sorry
lemma eq_204 : sorry := sorry
lemma eq_205 : sorry := sorry
lemma eq_206 : sorry := sorry
lemma eq_207 : sorry := sorry
lemma eq_208 : sorry := sorry
lemma eq_209 : sorry := sorry
lemma eq_210 : sorry := sorry
lemma eq_211 : sorry := sorry
lemma eq_212 : sorry := sorry
lemma eq_213 : sorry := sorry
lemma eq_214 : sorry := sorry
lemma eq_215 : sorry := sorry
lemma eq_216 : sorry := sorry

/-! ### Definition -/

lemma eq_217 : sorry := sorry
lemma eq_218 : sorry := sorry
lemma eq_219 : sorry := sorry
lemma eq_220 : sorry := sorry

/-! ### Properties -/

lemma eq_221 : sorry := sorry
lemma eq_222 : sorry := sorry

/-! ### Construction -/

lemma eq_223 : sorry := sorry
lemma eq_224 : sorry := sorry

end matrix_cookbook
