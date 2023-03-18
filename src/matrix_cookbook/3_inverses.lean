import linear_algebra.matrix.nonsingular_inverse
import data.complex.basic

namespace matrix_cookbook
variables {m n p : Type*}
variables [fintype m] [fintype n] [fintype p]
variables [decidable_eq m] [decidable_eq n] [decidable_eq p]
variables (A B C : matrix n n ℂ)
open matrix
open_locale matrix big_operators

/-! # Inverses -/

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
