import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic

/-! # Inverses -/


namespace MatrixCookbook

variable {m n p : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

variable (A B C : Matrix n n ℂ)

open Matrix

open scoped Matrix BigOperators

/-! ## Basic -/


/-! ### Definition -/


theorem eq_145 (h : IsUnit A.det) : A * A⁻¹ = 1 ∧ A⁻¹ * A = 1 :=
  ⟨mul_nonsing_inv _ h, nonsing_inv_mul _ h⟩

/-! ### Cofactors and Adjoint -/


-- mathlib has no need for this due to `eq_148`, but we include it for completeness
@[reducible]
def cofactor {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) ℂ) :
    Matrix (Fin n.succ) (Fin n.succ) ℂ :=
  of fun i j : Fin n.succ => (-1) ^ (i + j : ℕ) * det (A.submatrix i.succAboveEmb j.succAboveEmb)

theorem eq_146 {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) ℂ) (i j : Fin n.succ) :
    cofactor A i j = (-1) ^ (i + j : ℕ) * det (A.submatrix i.succAboveEmb j.succAboveEmb) :=
  rfl

theorem eq_147 {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) ℂ) :
    cofactor A = of fun i j => cofactor A i j :=
  rfl

-- eq_147 is a trivial matrix definiton!
theorem eq_148 {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) ℂ) : adjugate A = (cofactor A)ᵀ :=
  Matrix.ext <| adjugate_fin_succ_eq_det_submatrix _

/-! ### Determinant -/


/-- Note: adapted from column 0 to column 1. -/
theorem eq_149 (n : ℕ) (A : Matrix (Fin n.succ) (Fin n.succ) ℂ) :
    det A = ∑ i : Fin n.succ, (-1) ^ (i : ℕ) * A i 0 * det (A.submatrix i.succAboveEmb Fin.succ) :=
  det_succ_column_zero _

theorem eq_150 (n : ℕ) (A : Matrix (Fin n.succ) (Fin n.succ) ℂ) :
    det A = ∑ j : Fin n.succ, A 0 j * adjugate A j 0 :=
  det_eq_sum_mul_adjugate_row _ _

/-! ### Construction -/


theorem eq_151 : A⁻¹ = (1 / A.det) • adjugate A := by rw [inv_def, Ring.inverse_eq_inv, one_div]

/-! ### Condition number -/


theorem eq_152 : sorry :=
  sorry

theorem eq_153 : sorry :=
  sorry

theorem eq_154 : sorry :=
  sorry

/-! ## Exact Relations -/


/-! ### Basic -/


theorem eq_155 (A B : Matrix m m ℂ) : (A * B)⁻¹ = B⁻¹ * A⁻¹ :=
  mul_inv_rev _ _

/-! ### The Woodbury identity -/


theorem eq_156 : sorry :=
  sorry

theorem eq_157 : sorry :=
  sorry

theorem eq_158 : sorry :=
  sorry

/-! ### The Kailath Variant -/


theorem eq_159 (B : Matrix n m ℂ) (C : Matrix m n ℂ) :
    (A + B * C)⁻¹ = A⁻¹ - A⁻¹ * B * (1 + C * A⁻¹ * B)⁻¹ * C * A⁻¹ :=
  sorry

/-! ### Sherman-Morrison -/


theorem eq_160 (b c : n → ℂ) :
    (A + col b * row c)⁻¹ = A⁻¹ - (1 + c ⬝ᵥ A⁻¹.mulVec b)⁻¹ • A⁻¹ * (col b * row c) * A⁻¹ := by
  rw [eq_159, ← Matrix.mul_assoc _ (col b), Matrix.mul_assoc _ (row c), Matrix.mul_assoc _ (row c),
    Matrix.smul_mul]
  congr
  sorry

/-! ### The Searle Set of Identities -/


theorem eq_161 : (1 + A⁻¹)⁻¹ = A * (A + 1)⁻¹ :=
  sorry

theorem eq_162 : (A + Bᵀ * B)⁻¹ * B = A⁻¹ * B * (1 + Bᵀ * A⁻¹ * B)⁻¹ :=
  sorry

theorem eq_163 : (A⁻¹ + B⁻¹)⁻¹ = A * (A + B)⁻¹ * B ∧ (A⁻¹ + B⁻¹)⁻¹ = B * (A + B)⁻¹ * A :=
  sorry

theorem eq_164 : A - A * (A + B)⁻¹ * A = B - B * (A + B)⁻¹ * B :=
  sorry

theorem eq_165 : A⁻¹ + B⁻¹ = A⁻¹ * (A + B)⁻¹ * B⁻¹ :=
  sorry

theorem eq_166 : (1 + A * B)⁻¹ = 1 - A * (1 + B * A)⁻¹ * B :=
  sorry

theorem eq_167 : (1 + A * B)⁻¹ * A = A * (1 + B * A)⁻¹ :=
  sorry

/-! ### Rank-1 update of inverse of inner product -/


/-! ### Rank-1 update of Moore-Penrose Inverse -/


theorem eq_168 : sorry :=
  sorry

theorem eq_169 : sorry :=
  sorry

theorem eq_170 : sorry :=
  sorry

theorem eq_171 : sorry :=
  sorry

theorem eq_172 : sorry :=
  sorry

theorem eq_173 : sorry :=
  sorry

theorem eq_174 : sorry :=
  sorry

theorem eq_175 : sorry :=
  sorry

theorem eq_176 : sorry :=
  sorry

theorem eq_177 : sorry :=
  sorry

theorem eq_178 : sorry :=
  sorry

theorem eq_179 : sorry :=
  sorry

theorem eq_180 : sorry :=
  sorry

theorem eq_181 : sorry :=
  sorry

theorem eq_182 : sorry :=
  sorry

theorem eq_183 : sorry :=
  sorry

/-! ## Implication on Inverses -/


theorem eq_184 : (A + B)⁻¹ = A⁻¹ + B⁻¹ → A * B⁻¹ * A = B * A⁻¹ * B :=
  sorry

/-! ### A PosDef identity -/


theorem eq_185 : sorry :=
  sorry

/-! ## Approximations -/


theorem eq_186 : sorry :=
  sorry

theorem eq_187 : sorry :=
  sorry

theorem eq_188 : sorry :=
  sorry

theorem eq_189 : sorry :=
  sorry

theorem eq_190 : sorry :=
  sorry

theorem eq_191 : sorry :=
  sorry

theorem eq_192 : sorry :=
  sorry

theorem eq_193 : sorry :=
  sorry

theorem eq_194 : sorry :=
  sorry

theorem eq_195 : sorry :=
  sorry

theorem eq_196 : sorry :=
  sorry

theorem eq_197 : sorry :=
  sorry

/-! ## Generalized Inverse -/


theorem eq_198 : sorry :=
  sorry

/-! ### Definition -/


/-! ## Pseudo Inverse -/


theorem eq_199 : sorry :=
  sorry

theorem eq_200 : sorry :=
  sorry

theorem eq_201 : sorry :=
  sorry

theorem eq_202 : sorry :=
  sorry

theorem eq_203 : sorry :=
  sorry

theorem eq_204 : sorry :=
  sorry

theorem eq_205 : sorry :=
  sorry

theorem eq_206 : sorry :=
  sorry

theorem eq_207 : sorry :=
  sorry

theorem eq_208 : sorry :=
  sorry

theorem eq_209 : sorry :=
  sorry

theorem eq_210 : sorry :=
  sorry

theorem eq_211 : sorry :=
  sorry

theorem eq_212 : sorry :=
  sorry

theorem eq_213 : sorry :=
  sorry

theorem eq_214 : sorry :=
  sorry

theorem eq_215 : sorry :=
  sorry

theorem eq_216 : sorry :=
  sorry

/-! ### Definition -/


theorem eq_217 : sorry :=
  sorry

theorem eq_218 : sorry :=
  sorry

theorem eq_219 : sorry :=
  sorry

theorem eq_220 : sorry :=
  sorry

/-! ### Properties -/


theorem eq_221 : sorry :=
  sorry

theorem eq_222 : sorry :=
  sorry

/-! ### Construction -/


theorem eq_223 : sorry :=
  sorry

theorem eq_224 : sorry :=
  sorry

end MatrixCookbook

