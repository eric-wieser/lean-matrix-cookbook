import linear_algebra.matrix.ldl

/-! # Solutions and Decompositions -/

variables {m n p : Type*}
variables [fintype m] [fintype n] [fintype p]
variables [decidable_eq m] [decidable_eq n] [decidable_eq p]

open_locale matrix

namespace matrix_cookbook

/-! ## Solutions to linear equations -/

/-! ### Simple Linear Regression -/

lemma eq_260 : sorry := sorry

/-! ### Existence in Linear Systems -/

lemma eq_261 : sorry := sorry

/-! ### Standard Square -/

lemma eq_262 : sorry := sorry

/-! ### Degenerated Square -/

/-! ### Cramer's rule -/

lemma eq_263 : sorry := sorry
lemma eq_264 : sorry := sorry

/-! ### Over-determined Rectangular -/

lemma eq_265 : sorry := sorry
lemma eq_266 : sorry := sorry

/-! ### Under-determined Rectangular -/

lemma eq_267 : sorry := sorry
lemma eq_268 : sorry := sorry
lemma eq_269 : sorry := sorry

/-! ### Linear form and zeros -/

lemma eq_270 : sorry := sorry

/-! ### Square form and zeros -/

lemma eq_271 : sorry := sorry

/-! ### The Lyapunov Equation -/

lemma eq_272 : sorry := sorry
lemma eq_273 : sorry := sorry

/-! ### Encapsulating Sum -/

lemma eq_274 : sorry := sorry
lemma eq_275 : sorry := sorry

/-! ## Eigenvalues and Eigenvectors -/

/-! ### Definition -/

lemma eq_276 : sorry := sorry

/-! ### Decompositions -/

lemma eq_277 : sorry := sorry
lemma eq_278 : sorry := sorry
lemma eq_279 : sorry := sorry

/-! ### General Properties -/

lemma eq_280 : sorry := sorry
lemma eq_281 : sorry := sorry

/-! ### Symmetric -/

lemma eq_282 : sorry := sorry
lemma eq_283 : sorry := sorry
lemma eq_284 : sorry := sorry
lemma eq_285 : sorry := sorry
lemma eq_286 : sorry := sorry
lemma eq_287 : sorry := sorry
lemma eq_288 : sorry := sorry

/-! ### Characteristic polynomial -/

lemma eq_289 : sorry := sorry
lemma eq_290 : sorry := sorry

/-! ## Singular Value Decomposition -/

lemma eq_291 : sorry := sorry
lemma eq_292 : sorry := sorry

/-! ### Symmetric Square decomposed into squares -/

lemma eq_293 : sorry := sorry

/-! ### Square decomposed into squares -/

lemma eq_294 : sorry := sorry

/-! ### Square decomposed into rectangular -/

lemma eq_295 : sorry := sorry

/-! ### Rectangular decomposition I -/

lemma eq_296 : sorry := sorry

/-! ### Rectangular decomposition II -/

lemma eq_297 : sorry := sorry

/-! ### Rectangular decomposition III -/

lemma eq_298 : sorry := sorry

/-! ## Triangular Decomposition -/

/-! ## LU decomposition -/

lemma eq_299 : sorry := sorry

/-! ### Cholesky-decomposition -/

lemma eq_300 : sorry := sorry

/-! ## LDM decomposition -/

lemma eq_301 : sorry := sorry

/-! ## LDL decompositions -/

lemma eq_302 {n : ℕ} (A : matrix (fin n) (fin n) ℝ) (hA : A.pos_def) :
  A = LDL.lower hA ⬝ LDL.diag hA ⬝ (LDL.lower hA)ᴴ := (LDL.lower_conj_diag hA).symm

end matrix_cookbook