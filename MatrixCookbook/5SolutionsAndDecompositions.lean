import Mathlib.LinearAlgebra.Matrix.LDL
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Matrix.Vec

/-! # Solutions and Decompositions -/


variable {m n p R : Type*}

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


theorem eq_262 [Field R] (A : Matrix n n R) (x b : n → R) (h : IsUnit A) :
    A *ᵥ x = b ↔ x = A⁻¹ *ᵥ b := by
  conv_rhs => rw [← Matrix.mulVec_injective_of_isUnit h|>.eq_iff]
  letI := h.invertible
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

/-! ### Degenerated Square -/


/-! ### Cramer's rule -/

/-- This isn't a theorem at all. -/
theorem eq_263 : True :=
  trivial

theorem eq_264 [Field R] (A : Matrix n n R) (x b : n → R) (h : A.det ≠ 0) :
    A *ᵥ x = b ↔ ∀ i, x i = A.det⁻¹ • A.cramerMap b i :=
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


theorem eq_270 (A : Matrix m m ℝ) : (∀ x, A.mulVec x = 0) → A = 0 := by
  intro h
  ext i j
  simpa using congr_fun (h (Pi.single j 1)) i

/-! ### Square form and zeros -/


theorem eq_271 (A : Matrix m m ℝ) (hA : A.IsSymm) : (∀ x, x ⬝ᵥ A.mulVec x = 0) → A = 0 :=
  sorry

/-! ### The Lyapunov Equation -/

/-- This is actually an assumption for the next equation. -/
theorem eq_272 : True := trivial

open scoped Kronecker in
theorem eq_273 (A : Matrix n n ℝ) (B : Matrix n n ℝ) (X : Matrix n n ℝ) (C : Matrix n n ℝ)
    (h : IsUnit (1 ⊗ₖ A + Bᵀ ⊗ₖ 1)) :
    A * X + X * B = C ↔ X.vec = (1 ⊗ₖ A + Bᵀ ⊗ₖ 1)⁻¹ *ᵥ C.vec := by
  letI := h.invertible
  rw [← Matrix.mulVec_injective_of_isUnit h |>.eq_iff, Matrix.mulVec_mulVec,
    Matrix.mul_inv_of_invertible, Matrix.one_mulVec, Matrix.add_mulVec, Matrix.kronecker_mulVec_vec,
    Matrix.kronecker_mulVec_vec, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
    ← Matrix.vec_add, Matrix.transpose_transpose, Matrix.vec_inj]

/-! ### Encapsulating Sum -/

/-- This is actually an assumption for the next equation. -/
theorem eq_274 : True := trivial

open scoped Kronecker in
theorem eq_275 [Fintype ι] (A : ι → Matrix n n ℝ) (B : ι → Matrix n n ℝ) (X : Matrix n n ℝ) (C : Matrix n n ℝ)
    (h : IsUnit (∑ i, (B i)ᵀ ⊗ₖ A i)) :
    ∑ i, A i * X * B i = C ↔ X.vec = (∑ i, (B i)ᵀ ⊗ₖ A i)⁻¹ *ᵥ C.vec := by
  letI := h.invertible
  rw [← Matrix.mulVec_injective_of_isUnit h |>.eq_iff, Matrix.mulVec_mulVec,
    Matrix.mul_inv_of_invertible, Matrix.one_mulVec, ← funext <| Matrix.mulVec.addMonoidHomLeft_apply _ _,
    map_sum]
  simp_rw [funext <| Matrix.mulVec.addMonoidHomLeft_apply _ _, Matrix.kronecker_mulVec_vec,
    Matrix.transpose_transpose, ← Matrix.vec_sum, Matrix.vec_inj]


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


theorem eq_282 (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℝ) * hA.eigenvectorUnitaryᵀ = 1 := by
  simpa only [Matrix.mem_unitaryGroup_iff] using hA.eigenvectorUnitary.prop

theorem eq_283 (A : Matrix n n ℝ) (hA : A.IsHermitian) (i : n) :
    (fun {α} (_ : α) => α) (hA.eigenvalues i) = ℝ :=
  rfl

theorem eq_284 (A : Matrix n n ℝ) (hA : A.IsHermitian) (p : ℕ):
    Matrix.trace (A ^ p) = ∑ i, hA.eigenvalues i ^ p := by
  have := hA.pow p
  sorry

theorem eq_285 (A : Matrix n n ℝ) (c : ℝ) (hA : A.IsHermitian) :
    (Matrix.isHermitian_one.add (hA.map (c • ·) (fun i => by aesop))).eigenvalues = 1 + c • hA.eigenvalues :=
  sorry

theorem eq_286 (A : Matrix n n ℝ) (hA : A.IsHermitian) (c : ℝ) :
    (hA.sub <| Matrix.isHermitian_diagonal fun _ => c).eigenvalues = hA.eigenvalues - Function.const _ c :=
  sorry

theorem eq_287 (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    hA.inv.eigenvalues = hA.eigenvalues⁻¹ := by
  sorry

theorem eq_288 (A : Matrix n n ℝ) (hA : A.PosDef) :
    (A.isHermitian_transpose_mul_self).eigenvalues = (A.isHermitian_mul_conjTranspose_self).eigenvalues ∧
    (A.isHermitian_mul_conjTranspose_self).eigenvalues = hA.isHermitian.eigenvalues^2 := by
  constructor
  · congr!
    · exact hA.isHermitian
    · exact hA.isHermitian.symm
  · sorry

/-! ### Characteristic polynomial -/

theorem eq_289 (A : Matrix m m ℝ) (γ : ℝ) : (-A).charpoly.eval (-γ) = (A - Matrix.scalar _ γ).det := by
  rw [Matrix.eval_charpoly, map_neg, neg_sub_neg]

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
