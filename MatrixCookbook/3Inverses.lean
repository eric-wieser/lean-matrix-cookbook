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


theorem eq152 : sorry :=
  sorry

theorem eq153 : sorry :=
  sorry

theorem eq154 : sorry :=
  sorry

/-! ## Exact Relations -/


/-! ### Basic -/


theorem eq_155 (A B : Matrix m m ℂ) : (A * B)⁻¹ = B⁻¹ * A⁻¹ :=
  mul_inv_rev _ _

/-! ### The Woodbury identity -/


theorem eq156 : sorry :=
  sorry

theorem eq157 : sorry :=
  sorry

theorem eq158 : sorry :=
  sorry

/-! ### The Kailath Variant -/


theorem eq_159 (B : Matrix n m ℂ) (C : Matrix m n ℂ) :
    (A + B ⬝ C)⁻¹ = A⁻¹ - A⁻¹ ⬝ B ⬝ (1 + C ⬝ A⁻¹ ⬝ B)⁻¹ ⬝ C ⬝ A⁻¹ :=
  sorry

/-! ### Sherman-Morrison -/


theorem eq_160 (b c : n → ℂ) :
    (A + col b ⬝ row c)⁻¹ = A⁻¹ - (1 + c ⬝ᵥ A⁻¹.mulVec b)⁻¹ • A⁻¹ ⬝ (col b ⬝ row c) ⬝ A⁻¹ := by
  rw [eq_159, ← Matrix.mul_assoc _ (col b), Matrix.mul_assoc _ (row c), Matrix.mul_assoc _ (row c),
    ← Matrix.mul_smul, Matrix.mul_assoc _ _ (row c ⬝ _)]
  congr
  sorry

/-! ### The Searle Set of Identities -/


theorem eq_161 : (1 + A⁻¹)⁻¹ = A ⬝ (A + 1)⁻¹ :=
  sorry

theorem eq_162 : (A + Bᵀ ⬝ B)⁻¹ ⬝ B = A⁻¹ ⬝ B ⬝ (1 + Bᵀ ⬝ A⁻¹ ⬝ B)⁻¹ :=
  sorry

theorem eq_163 : (A⁻¹ + B⁻¹)⁻¹ = A ⬝ (A + B)⁻¹ ⬝ B ∧ (A⁻¹ + B⁻¹)⁻¹ = B ⬝ (A + B)⁻¹ ⬝ A :=
  sorry

theorem eq_164 : A - A ⬝ (A + B)⁻¹ ⬝ A = B - B ⬝ (A + B)⁻¹ ⬝ B :=
  sorry

theorem eq_165 : A⁻¹ + B⁻¹ = A⁻¹ ⬝ (A + B)⁻¹ ⬝ B⁻¹ :=
  sorry

theorem eq_166 : (1 + A ⬝ B)⁻¹ = 1 - A ⬝ (1 + B ⬝ A)⁻¹ ⬝ B :=
  sorry

theorem eq_167 : (1 + A ⬝ B)⁻¹ ⬝ A = A ⬝ (1 + B ⬝ A)⁻¹ :=
  sorry

/-! ### Rank-1 update of inverse of inner product -/


/-! ### Rank-1 update of Moore-Penrose Inverse -/


theorem eq168 : sorry :=
  sorry

theorem eq169 : sorry :=
  sorry

theorem eq170 : sorry :=
  sorry

theorem eq171 : sorry :=
  sorry

theorem eq172 : sorry :=
  sorry

theorem eq173 : sorry :=
  sorry

theorem eq174 : sorry :=
  sorry

theorem eq175 : sorry :=
  sorry

theorem eq176 : sorry :=
  sorry

theorem eq177 : sorry :=
  sorry

theorem eq178 : sorry :=
  sorry

theorem eq179 : sorry :=
  sorry

theorem eq180 : sorry :=
  sorry

theorem eq181 : sorry :=
  sorry

theorem eq182 : sorry :=
  sorry

theorem eq183 : sorry :=
  sorry

/-! ## Implication on Inverses -/


theorem eq_184 : (A + B)⁻¹ = A⁻¹ + B⁻¹ → A ⬝ B⁻¹ ⬝ A = B ⬝ A⁻¹ ⬝ B :=
  sorry

/-! ### A PosDef identity -/


theorem eq185 : sorry :=
  sorry

/-! ## Approximations -/


theorem eq186 : sorry :=
  sorry

theorem eq187 : sorry :=
  sorry

theorem eq188 : sorry :=
  sorry

theorem eq189 : sorry :=
  sorry

theorem eq190 : sorry :=
  sorry

theorem eq191 : sorry :=
  sorry

theorem eq192 : sorry :=
  sorry

theorem eq193 : sorry :=
  sorry

theorem eq194 : sorry :=
  sorry

theorem eq195 : sorry :=
  sorry

theorem eq196 : sorry :=
  sorry

theorem eq197 : sorry :=
  sorry

/-! ## Generalized Inverse -/


theorem eq198 : sorry :=
  sorry

/-! ### Definition -/


/-! ## Pseudo Inverse -/


theorem eq199 : sorry :=
  sorry

theorem eq200 : sorry :=
  sorry

theorem eq201 : sorry :=
  sorry

theorem eq202 : sorry :=
  sorry

theorem eq203 : sorry :=
  sorry

theorem eq204 : sorry :=
  sorry

theorem eq205 : sorry :=
  sorry

theorem eq206 : sorry :=
  sorry

theorem eq207 : sorry :=
  sorry

theorem eq208 : sorry :=
  sorry

theorem eq209 : sorry :=
  sorry

theorem eq210 : sorry :=
  sorry

theorem eq211 : sorry :=
  sorry

theorem eq212 : sorry :=
  sorry

theorem eq213 : sorry :=
  sorry

theorem eq214 : sorry :=
  sorry

theorem eq215 : sorry :=
  sorry

theorem eq216 : sorry :=
  sorry

/-! ### Definition -/


theorem eq217 : sorry :=
  sorry

theorem eq218 : sorry :=
  sorry

theorem eq219 : sorry :=
  sorry

theorem eq220 : sorry :=
  sorry

/-! ### Properties -/


theorem eq221 : sorry :=
  sorry

theorem eq222 : sorry :=
  sorry

/-! ### Construction -/


theorem eq223 : sorry :=
  sorry

theorem eq224 : sorry :=
  sorry

end MatrixCookbook

