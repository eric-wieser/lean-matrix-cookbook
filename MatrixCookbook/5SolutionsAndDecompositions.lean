import Mathlib.LinearAlgebra.Matrix.LDL

/-! # Solutions and Decompositions -/


variable {m n p : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

open scoped Matrix

namespace MatrixCookbook

/-! ## Solutions to linear equations -/


/-! ### Simple Linear Regression -/


theorem eq_260 : (sorry : Prop) :=
  sorry

/-! ### Existence in Linear Systems -/


theorem eq_261 : (sorry : Prop) :=
  sorry

/-! ### Standard Square -/


theorem eq_262 : (sorry : Prop) :=
  sorry

/-! ### Degenerated Square -/


/-! ### Cramer's rule -/


theorem eq_263 : (sorry : Prop) :=
  sorry

theorem eq_264 : (sorry : Prop) :=
  sorry

/-! ### Over-determined Rectangular -/


theorem eq_265 : (sorry : Prop) :=
  sorry

theorem eq_266 : (sorry : Prop) :=
  sorry

/-! ### Under-determined Rectangular -/


theorem eq_267 : (sorry : Prop) :=
  sorry

theorem eq_268 : (sorry : Prop) :=
  sorry

theorem eq_269 : (sorry : Prop) :=
  sorry

/-! ### Linear form and zeros -/


theorem eq_270 (A : Matrix m m ℝ) : (∀ x, A.mulVec x = 0) → A = 0 :=
  sorry

/-! ### Square form and zeros -/


theorem eq_271 (A : Matrix m m ℝ) (hA : A.IsSymm) : (∀ x, x ⬝ᵥ A.mulVec x = 0) → A = 0 :=
  sorry

/-! ### The Lyapunov Equation -/


theorem eq_272 : (sorry : Prop) :=
  sorry

theorem eq_273 : (sorry : Prop) :=
  sorry

/-! ### Encapsulating Sum -/


theorem eq_274 : (sorry : Prop) :=
  sorry

theorem eq_275 : (sorry : Prop) :=
  sorry

/-! ## Eigenvalues and Eigenvectors -/


/-! ### Definition -/


theorem eq_276 : (sorry : Prop) :=
  sorry

/-! ### Decompositions -/


theorem eq_277 : (sorry : Prop) :=
  sorry

theorem eq_278 : (sorry : Prop) :=
  sorry

theorem eq_279 : (sorry : Prop) :=
  sorry

/-! ### General Properties -/


theorem eq_280 : (sorry : Prop) :=
  sorry

theorem eq_281 : (sorry : Prop) :=
  sorry

/-! ### Symmetric -/


theorem eq_282 : (sorry : Prop) :=
  sorry

theorem eq_283 : (sorry : Prop) :=
  sorry

theorem eq_284 : (sorry : Prop) :=
  sorry

theorem eq_285 : (sorry : Prop) :=
  sorry

theorem eq_286 : (sorry : Prop) :=
  sorry

theorem eq_287 : (sorry : Prop) :=
  sorry

theorem eq_288 : (sorry : Prop) :=
  sorry

/-! ### Characteristic polynomial -/


theorem eq_289 : (sorry : Prop) :=
  sorry

theorem eq_290 : (sorry : Prop) :=
  sorry

/-! ## Singular Value Decomposition -/


theorem eq_291 : (sorry : Prop) :=
  sorry

theorem eq_292 : (sorry : Prop) :=
  sorry

/-! ### Symmetric Square decomposed into squares -/


theorem eq_293 : (sorry : Prop) :=
  sorry

/-! ### Square decomposed into squares -/


theorem eq_294 : (sorry : Prop) :=
  sorry

/-! ### Square decomposed into rectangular -/


theorem eq_295 : (sorry : Prop) :=
  sorry

/-! ### Rectangular decomposition I -/


theorem eq_296 : (sorry : Prop) :=
  sorry

/-! ### Rectangular decomposition II -/


theorem eq_297 : (sorry : Prop) :=
  sorry

/-! ### Rectangular decomposition III -/


theorem eq_298 : (sorry : Prop) :=
  sorry

/-! ## Triangular Decomposition -/


/-! ## LU decomposition -/


theorem eq_299 : (sorry : Prop) :=
  sorry

/-! ### Cholesky-decomposition -/


theorem eq_300 : (sorry : Prop) :=
  sorry

/-! ## LDM decomposition -/


theorem eq_301 : (sorry : Prop) :=
  sorry

/-! ## LDL decompositions -/


theorem eq_302 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    A = LDL.lower hA * LDL.diag hA * (LDL.lower hA)ᴴ :=
  (LDL.lower_conj_diag hA).symm

end MatrixCookbook
