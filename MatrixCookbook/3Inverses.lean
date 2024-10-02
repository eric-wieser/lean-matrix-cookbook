import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import MatrixCookbook.ForMathlib.Data.Matrix

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


theorem eq_152 : (sorry : Prop) :=
  sorry

theorem eq_153 : (sorry : Prop) :=
  sorry

theorem eq_154 : (sorry : Prop) :=
  sorry

/-! ## Exact Relations -/


/-! ### Basic -/


theorem eq_155 (A B : Matrix m m ℂ) : (A * B)⁻¹ = B⁻¹ * A⁻¹ :=
  mul_inv_rev _ _

/-! ### The Woodbury identity -/


theorem eq_156
    (A : Matrix n n ℂ) (B : Matrix m m ℂ) (C : Matrix n m ℂ)
    (hA : IsUnit A) (hB : IsUnit B) (h : IsUnit (B⁻¹ + Cᵀ*A⁻¹*C)) :
    (A + C * B * Cᵀ)⁻¹ = A⁻¹ - A⁻¹ * C * (B⁻¹ + Cᵀ*A⁻¹*C)⁻¹ * Cᵀ * A⁻¹ :=
  Matrix.add_mul_mul_inv_eq_sub _ _ _ _ hA hB h

theorem eq_157 (A : Matrix n n ℂ) (B : Matrix m m ℂ) (U : Matrix n m ℂ) (V : Matrix m n ℂ)
    (hA : IsUnit A) (hB : IsUnit B) (h : IsUnit (B⁻¹ + V*A⁻¹*U)) :
    (A + U * B * V)⁻¹ = A⁻¹ - A⁻¹ * U * (B⁻¹ + V*A⁻¹*U)⁻¹ * V * A⁻¹ :=
  Matrix.add_mul_mul_inv_eq_sub _ _ _ _ hA hB h

open scoped ComplexOrder in
theorem eq_158 (P : Matrix n n ℂ) (R : Matrix m m ℂ) (B : Matrix m n ℂ)
    (hP : P.PosDef) (hR : R.PosDef) :
    (P + Bᵀ * R * B)⁻¹ * Bᵀ * R⁻¹ = P * Bᵀ * (B*P⁻¹*Bᵀ + R)⁻¹ := by
  sorry

/-! ### The Kailath Variant -/

theorem eq_159 (B : Matrix n m ℂ) (C : Matrix m n ℂ)
    (hA : IsUnit A) (h : IsUnit (1 + C * A⁻¹ * B)) :
    (A + B * C)⁻¹ = A⁻¹ - A⁻¹ * B * (1 + C * A⁻¹ * B)⁻¹ * C * A⁻¹ := by
  have := Matrix.add_mul_mul_inv_eq_sub A B _ C hA isUnit_one (by simpa using h)
  simpa using this

/-! ### Sherman-Morrison -/


theorem eq_160 (b c : n → ℂ) (hA : IsUnit A) (h : 1 + c ⬝ᵥ A⁻¹ *ᵥ b ≠ 0) :
    (A + col Unit b * row Unit c)⁻¹ = A⁻¹ - (1 + c ⬝ᵥ A⁻¹ *ᵥ b)⁻¹ • A⁻¹ * (col Unit b * row Unit c) * A⁻¹ := by
  rw [eq_159 _ _ _ hA, ← Matrix.mul_assoc _ (col Unit b), Matrix.mul_assoc _ (row Unit c), Matrix.mul_assoc _ (row Unit c),
    Matrix.smul_mul]
  · congr
    rw [← col_mulVec, ← row_vecMul, row_mul_col, smul_eq_mul_diagonal,
      Matrix.inv_subsingleton (m := Unit)]
    simp_rw [Ring.inverse_eq_inv]
    simp [← dotProduct_mulVec]
  · rw [isUnit_iff_isUnit_det, det_unique, add_apply, one_apply_eq]
    rw [← col_mulVec, ← row_vecMul, row_mulVec_eq_const, ← dotProduct_mulVec, isUnit_iff_ne_zero]
    exact h

/-! ### The Searle Set of Identities -/


theorem eq_161 : (1 + A⁻¹)⁻¹ = A * (A + 1)⁻¹ :=
  sorry

theorem eq_162 : (A + Bᵀ * B)⁻¹ * B = A⁻¹ * B * (1 + Bᵀ * A⁻¹ * B)⁻¹ :=
  sorry

theorem eq_163 (hA : IsUnit A) (hB : IsUnit B) :
    (A⁻¹ + B⁻¹)⁻¹ = A * (A + B)⁻¹ * B ∧ (A⁻¹ + B⁻¹)⁻¹ = B * (A + B)⁻¹ * A := by
  letI := hA.invertible; letI := hB.invertible
  conv_lhs => rw [add_comm]
  rw [Matrix.inv_add_inv (iff_of_true hA hB), Matrix.inv_add_inv (iff_of_true hB hA)]
  simp_rw [Matrix.mul_inv_rev, Matrix.inv_inv_of_invertible, mul_assoc, add_comm]
  simp

theorem eq_164 : A - A * (A + B)⁻¹ * A = B - B * (A + B)⁻¹ * B :=
  sorry

theorem eq_165 (hA : IsUnit A) (hB : IsUnit B) : A⁻¹ + B⁻¹ = A⁻¹ * (A + B) * B⁻¹ :=
  Matrix.inv_add_inv <| iff_of_true hA hB

theorem eq_166 : (1 + A * B)⁻¹ = 1 - A * (1 + B * A)⁻¹ * B :=
  sorry

theorem eq_167 : (1 + A * B)⁻¹ * A = A * (1 + B * A)⁻¹ :=
  sorry

/-! ### Rank-1 update of inverse of inner product -/


/-! ### Rank-1 update of Moore-Penrose Inverse -/


theorem eq_168 : (sorry : Prop) :=
  sorry

theorem eq_169 : (sorry : Prop) :=
  sorry

theorem eq_170 : (sorry : Prop) :=
  sorry

theorem eq_171 : (sorry : Prop) :=
  sorry

theorem eq_172 : (sorry : Prop) :=
  sorry

theorem eq_173 : (sorry : Prop) :=
  sorry

theorem eq_174 : (sorry : Prop) :=
  sorry

theorem eq_175 : (sorry : Prop) :=
  sorry

theorem eq_176 : (sorry : Prop) :=
  sorry

theorem eq_177 : (sorry : Prop) :=
  sorry

theorem eq_178 : (sorry : Prop) :=
  sorry

theorem eq_179 : (sorry : Prop) :=
  sorry

theorem eq_180 : (sorry : Prop) :=
  sorry

theorem eq_181 : (sorry : Prop) :=
  sorry

theorem eq_182 : (sorry : Prop) :=
  sorry

theorem eq_183 : (sorry : Prop) :=
  sorry

/-! ## Implication on Inverses -/


theorem eq_184 : (A + B)⁻¹ = A⁻¹ + B⁻¹ → A * B⁻¹ * A = B * A⁻¹ * B :=
  sorry

/-! ### A PosDef identity -/


theorem eq_185 : (sorry : Prop) :=
  sorry

/-! ## Approximations -/


theorem eq_186 : (sorry : Prop) :=
  sorry

theorem eq_187 : (sorry : Prop) :=
  sorry

theorem eq_188 : (sorry : Prop) :=
  sorry

theorem eq_189 : (sorry : Prop) :=
  sorry

theorem eq_190 : (sorry : Prop) :=
  sorry

theorem eq_191 : (sorry : Prop) :=
  sorry

theorem eq_192 : (sorry : Prop) :=
  sorry

theorem eq_193 : (sorry : Prop) :=
  sorry

theorem eq_194 : (sorry : Prop) :=
  sorry

theorem eq_195 : (sorry : Prop) :=
  sorry

theorem eq_196 : (sorry : Prop) :=
  sorry

theorem eq_197 : (sorry : Prop) :=
  sorry

/-! ## Generalized Inverse -/


theorem eq_198 : (sorry : Prop) :=
  sorry

/-! ### Definition -/


/-! ## Pseudo Inverse -/


theorem eq_199 : (sorry : Prop) :=
  sorry

theorem eq_200 : (sorry : Prop) :=
  sorry

theorem eq_201 : (sorry : Prop) :=
  sorry

theorem eq_202 : (sorry : Prop) :=
  sorry

theorem eq_203 : (sorry : Prop) :=
  sorry

theorem eq_204 : (sorry : Prop) :=
  sorry

theorem eq_205 : (sorry : Prop) :=
  sorry

theorem eq_206 : (sorry : Prop) :=
  sorry

theorem eq_207 : (sorry : Prop) :=
  sorry

theorem eq_208 : (sorry : Prop) :=
  sorry

theorem eq_209 : (sorry : Prop) :=
  sorry

theorem eq_210 : (sorry : Prop) :=
  sorry

theorem eq_211 : (sorry : Prop) :=
  sorry

theorem eq_212 : (sorry : Prop) :=
  sorry

theorem eq_213 : (sorry : Prop) :=
  sorry

theorem eq_214 : (sorry : Prop) :=
  sorry

theorem eq_215 : (sorry : Prop) :=
  sorry

theorem eq_216 : (sorry : Prop) :=
  sorry

/-! ### Definition -/


theorem eq_217 : (sorry : Prop) :=
  sorry

theorem eq_218 : (sorry : Prop) :=
  sorry

theorem eq_219 : (sorry : Prop) :=
  sorry

theorem eq_220 : (sorry : Prop) :=
  sorry

/-! ### Properties -/


theorem eq_221 : (sorry : Prop) :=
  sorry

theorem eq_222 : (sorry : Prop) :=
  sorry

/-! ### Construction -/


theorem eq_223 : (sorry : Prop) :=
  sorry

theorem eq_224 : (sorry : Prop) :=
  sorry

end MatrixCookbook
