import linear_algebra.matrix.nonsingular_inverse
import data.complex.basic
import matrix_cookbook.for_mathlib.linear_algebra.matrix.nonsing_inverse
import tactic.swap_var

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

-- mathlib has no need for this due to `eq_148`, but we include it for completeness
@[reducible] def cofactor {n : ℕ} (A : matrix (fin n.succ) (fin n.succ) ℂ) :
  matrix (fin n.succ) (fin n.succ) ℂ := 
of (λ i j : fin n.succ, (-1)^(i + j : ℕ) * det (A.submatrix i.succ_above j.succ_above))

lemma eq_146 {n : ℕ} (A : matrix (fin n.succ) (fin n.succ) ℂ) (i j : fin n.succ) :
  cofactor A i j = (-1)^(i + j : ℕ) * det (A.submatrix i.succ_above j.succ_above) := rfl

lemma eq_147 {n : ℕ} (A : matrix (fin n.succ) (fin n.succ) ℂ) : 
  cofactor A = of (λ i j, cofactor A i j) := rfl -- eq_147 is a trivial matrix definiton!

lemma eq_148 {n : ℕ} (A : matrix (fin n.succ) (fin n.succ) ℂ) : adjugate A = (cofactor A)ᵀ :=
matrix.ext $ adjugate_fin_succ_eq_det_submatrix _

/-! ### Determinant -/

/-- Note: adapted from column 0 to column 1. -/
lemma eq_149 (n : ℕ) (A : matrix (fin n.succ) (fin n.succ) ℂ) :
  det A = ∑ i : fin n.succ, (-1) ^ (i : ℕ) * A i 0 * det (A.submatrix i.succ_above fin.succ) :=
det_succ_column_zero _
lemma eq_150 (n : ℕ) (A : matrix (fin n.succ) (fin n.succ) ℂ) :
  det A = ∑ j : fin n.succ, A 0 j * adjugate A j 0 := 
det_eq_sum_mul_adjugate_row _ _

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

lemma eq_156 : sorry := sorry
lemma eq_157 : sorry := sorry
lemma eq_158 : sorry := sorry

/-! ### The Kailath Variant -/

lemma eq_159 (B : matrix n m ℂ) (C : matrix m n ℂ) :
  (A + B⬝C)⁻¹ = A⁻¹ - A⁻¹⬝B⬝(1 + C⬝A⁻¹⬝B)⁻¹⬝C⬝A⁻¹ := sorry

/-! ### Sherman-Morrison -/

lemma eq_160 (b c : n → ℂ) :
  (A + col b ⬝ row c)⁻¹ = A⁻¹ - (1 + c ⬝ᵥ (A⁻¹.mul_vec b))⁻¹ • (A⁻¹⬝(col b ⬝ row c)⬝A⁻¹) :=
begin
  rw [eq_159, ←matrix.mul_assoc _ (col b), matrix.mul_assoc _ (row c), matrix.mul_assoc _ (row c),
    ←matrix.mul_smul, matrix.mul_assoc _ _ (row c ⬝ _)],
  congr,
  sorry
end

/-! ### The Searle Set of Identities -/

lemma eq_161 {hA: is_unit A.det} {hAaddOne: is_unit (A+1).det} :  (1 + A⁻¹)⁻¹ = A⬝(A + 1)⁻¹ :=
begin
  rw inv_eq_right_inv, 
  rw [matrix.add_mul, matrix.one_mul, nonsing_inv_mul_cancel_left],
  nth_rewrite 1 ← matrix.one_mul (A + 1)⁻¹,   
  rw [← matrix.add_mul, mul_nonsing_inv],
  assumption',
end
lemma eq_162 {B: matrix n m ℂ} {hAB: is_unit (1 + Bᵀ ⬝ A⁻¹ ⬝ B).det} : 
  (A + B⬝Bᵀ)⁻¹⬝B = A⁻¹⬝B⬝(1 + Bᵀ⬝A⁻¹⬝B)⁻¹:= 
begin
  rw [eq_159, matrix.sub_mul, sub_eq_iff_eq_add],
  repeat {rw matrix.mul_assoc (A⁻¹⬝B), },
  rw ← matrix.mul_add (A⁻¹⬝B),
  nth_rewrite 0 ← matrix.mul_one (1 + Bᵀ ⬝ A⁻¹ ⬝ B)⁻¹,
  repeat {rw matrix.mul_assoc (1 + Bᵀ ⬝ A⁻¹ ⬝ B)⁻¹, },
  rwa [← matrix.mul_add (1 + Bᵀ ⬝ A⁻¹ ⬝ B)⁻¹, nonsing_inv_mul, matrix.mul_one],
end
lemma eq_163 {hA: is_unit A.det} {hB: is_unit B.det} {hAB: is_unit (A + B).det}: 
  (A⁻¹ + B⁻¹)⁻¹ = A⬝(A + B)⁻¹⬝B ∧ (A⁻¹ + B⁻¹)⁻¹ = B⬝(A + B)⁻¹⬝A :=
begin
  split,
  work_on_goal 2 {swap_var [A B], rw add_comm, rw add_comm B,  },
  all_goals 
  { rw inv_eq_right_inv, 
    rw [matrix.add_mul, matrix.mul_assoc, nonsing_inv_mul_cancel_left],
    apply_fun (λ x, B⬝x), dsimp, 
    rw [matrix.mul_add, mul_nonsing_inv_cancel_left, ← matrix.add_mul, add_comm,
    mul_nonsing_inv_cancel_left,matrix.mul_one],},
  assumption',
  exact left_mul_inj_of_is_unit_det hB,
  rw add_comm, exact hAB,
  exact left_mul_inj_of_is_unit_det hA,
end

lemma eq_164_one_side (A B : matrix n n ℂ) (hA: is_unit A.det) (hB: is_unit B.det): 
  A - A⬝(A + B)⁻¹⬝A = (B⁻¹ + A⁻¹)⁻¹ := 
begin
  haveI invB := invertible_of_is_unit_det B hB,
  nth_rewrite 0 ← matrix.mul_one B,
  rw [eq_159, matrix.one_mul, matrix.mul_one, matrix.mul_sub, mul_nonsing_inv A hA, 
    matrix.sub_mul, matrix.one_mul, sub_sub_cancel,  matrix.mul_assoc _ _ A, 
    nonsing_inv_mul_cancel_right A _ hA, matrix.mul_assoc, mul_nonsing_inv_cancel_left A _ hA],
  nth_rewrite 0 ← inv_inv_of_invertible B,
  rw [← matrix.mul_inv_rev, matrix.add_mul, matrix.one_mul, mul_nonsing_inv_cancel_right B _ hB],
end

lemma eq_164 {hA: is_unit A.det} {hB: is_unit B.det}: 
  A - A⬝(A + B)⁻¹⬝A = B - B⬝(A + B)⁻¹⬝B :=
begin
  rw [eq_164_one_side A B hA hB, add_comm A, eq_164_one_side B A hB hA, add_comm],
end

lemma eq_165 {hA: is_unit A.det} {hB: is_unit B.det} : A⁻¹ + B⁻¹ = A⁻¹⬝(A + B)⬝B⁻¹ := 
begin 
  rw [matrix.mul_add, matrix.add_mul, mul_nonsing_inv_cancel_right B _ hB, 
    nonsing_inv_mul A hA, matrix.one_mul, add_comm],
end

lemma eq_166 {A: matrix n m ℂ} {B: matrix m n ℂ}: 
  (1 + A⬝B)⁻¹ = 1 - A⬝(1 + B⬝A)⁻¹⬝B :=
begin
  rw eq_159 1 A B, 
  simp only [inv_one, matrix.one_mul, matrix.mul_one],
end
lemma eq_167 (A: matrix m n ℂ)(B: matrix n m ℂ) {hAB: is_unit (1 + B⬝A).det}: 
  (1 + A⬝B)⁻¹⬝A = A⬝(1 + B⬝A)⁻¹ := 
begin
  rw [eq_159 1 A B, inv_one, matrix.one_mul, matrix.mul_one, matrix.mul_one,
    matrix.sub_mul, matrix.one_mul, sub_eq_iff_eq_add],
  nth_rewrite 0 ← matrix.mul_one (A ⬝ (1 + B ⬝ A)⁻¹),
  rwa [matrix.mul_assoc (A ⬝ (1 + B ⬝ A)⁻¹) _ _, ← matrix.mul_add (A ⬝ (1 + B ⬝ A)⁻¹) _ _,
    nonsing_inv_mul_cancel_right],
end

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
