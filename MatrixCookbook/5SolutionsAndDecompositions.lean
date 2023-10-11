import Mathlib.LinearAlgebra.Matrix.Ldl

/-! # Solutions and Decompositions -/


variable {m n p : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

open scoped Matrix

namespace MatrixCookbook

/-! ## Solutions to linear equations -/


/-! ### Simple Linear Regression -/


theorem eq260 : sorry :=
  sorry

/-! ### Existence in Linear Systems -/


theorem eq261 : sorry :=
  sorry

/-! ### Standard Square -/


theorem eq262 : sorry :=
  sorry

/-! ### Degenerated Square -/


/-! ### Cramer's rule -/


theorem eq263 : sorry :=
  sorry

theorem eq264 : sorry :=
  sorry

/-! ### Over-determined Rectangular -/


theorem eq265 : sorry :=
  sorry

theorem eq266 : sorry :=
  sorry

/-! ### Under-determined Rectangular -/


theorem eq267 : sorry :=
  sorry

theorem eq268 : sorry :=
  sorry

theorem eq269 : sorry :=
  sorry

/-! ### Linear form and zeros -/


theorem eq_270 (A : Matrix m m ℝ) : (∀ x, A.mulVec x = 0) → A = 0 :=
  sorry

/-! ### Square form and zeros -/


theorem eq_271 (A : Matrix m m ℝ) (hA : A.IsSymm) : (∀ x, x ⬝ᵥ A.mulVec x = 0) → A = 0 :=
  sorry

/-! ### The Lyapunov Equation -/


theorem eq272 : sorry :=
  sorry

theorem eq273 : sorry :=
  sorry

/-! ### Encapsulating Sum -/


theorem eq274 : sorry :=
  sorry

theorem eq275 : sorry :=
  sorry

/-! ## Eigenvalues and Eigenvectors -/


/-! ### Definition -/


theorem eq276 : sorry :=
  sorry

/-! ### Decompositions -/


theorem eq277 : sorry :=
  sorry

theorem eq278 : sorry :=
  sorry

theorem eq279 : sorry :=
  sorry

/-! ### General Properties -/


theorem eq280 : sorry :=
  sorry

theorem eq281 : sorry :=
  sorry

/-! ### Symmetric -/


theorem eq282 : sorry :=
  sorry

theorem eq283 : sorry :=
  sorry

theorem eq284 : sorry :=
  sorry

theorem eq285 : sorry :=
  sorry

theorem eq286 : sorry :=
  sorry

theorem eq287 : sorry :=
  sorry

theorem eq288 : sorry :=
  sorry

/-! ### Characteristic polynomial -/


theorem eq289 : sorry :=
  sorry

theorem eq290 : sorry :=
  sorry

/-! ## Singular Value Decomposition -/


theorem eq291 : sorry :=
  sorry

theorem eq292 : sorry :=
  sorry

/-! ### Symmetric Square decomposed into squares -/


theorem eq293 : sorry :=
  sorry

/-! ### Square decomposed into squares -/


theorem eq294 : sorry :=
  sorry

/-! ### Square decomposed into rectangular -/


theorem eq295 : sorry :=
  sorry

/-! ### Rectangular decomposition I -/


theorem eq296 : sorry :=
  sorry

/-! ### Rectangular decomposition II -/


theorem eq297 : sorry :=
  sorry

/-! ### Rectangular decomposition III -/


theorem eq298 : sorry :=
  sorry

/-! ## Triangular Decomposition -/


/-! ## LU decomposition -/


theorem eq299 : sorry :=
  sorry

/-! ### Cholesky-decomposition -/


theorem eq300 : sorry :=
  sorry

/-! ## LDM decomposition -/


theorem eq301 : sorry :=
  sorry

/-! ## LDL decompositions -/


theorem eq_302 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    A = LDL.lower hA ⬝ LDL.diag hA ⬝ (LDL.lower hA)ᴴ :=
  (LDL.lower_conj_diag hA).symm

end MatrixCookbook

