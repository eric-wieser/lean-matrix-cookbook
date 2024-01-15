import Mathlib.RingTheory.Complex

/-! # Complex Matrices -/


namespace MatrixCookbook

theorem eq_225 (z : ℂ) : Algebra.leftMulMatrix Complex.basisOneI z = !![z.re, -z.im; z.im, z.re] :=
  Algebra.leftMulMatrix_complex z

/-! ## Complex Derivatives -/


theorem eq_226 : sorry :=
  sorry

theorem eq_227 : sorry :=
  sorry

theorem eq_228 : sorry :=
  sorry

theorem eq_229 : sorry :=
  sorry

theorem eq_230 : sorry :=
  sorry

theorem eq_231 : sorry :=
  sorry

theorem eq_232 : sorry :=
  sorry

theorem eq_233 : sorry :=
  sorry

/-! ### The Chain Rule for complex numbers -/


theorem eq_234 : sorry :=
  sorry

theorem eq_235 : sorry :=
  sorry

/-! ### Complex Derivatives of Traces -/


theorem eq_236 : sorry :=
  sorry

theorem eq_237 : sorry :=
  sorry

theorem eq_238 : sorry :=
  sorry

theorem eq_239 : sorry :=
  sorry

theorem eq_240 : sorry :=
  sorry

theorem eq_241 : sorry :=
  sorry

theorem eq_242 : sorry :=
  sorry

theorem eq_243 : sorry :=
  sorry

theorem eq_244 : sorry :=
  sorry

theorem eq_245 : sorry :=
  sorry

theorem eq_246 : sorry :=
  sorry

theorem eq_247 : sorry :=
  sorry

theorem eq_248 : sorry :=
  sorry

/-! ### Complex Derivative Involving Determinants -/


theorem eq_249 : sorry :=
  sorry

theorem eq_250 : sorry :=
  sorry

/-! ## Higher order and non-linear derivatives -/


theorem eq_251 : sorry :=
  sorry

theorem eq_252 : sorry :=
  sorry

/-! ## Inverse of complex sum -/

section
variable [Fintype m] [DecidableEq m] (A B : Matrix m m ℝ) {t : ℝ}

local notation "E" => A + t • B
local notation "F" => B - t • A

open Complex (I)

theorem eq_253 : E = A + t • B := rfl

theorem eq_254 : F = B - t • A := rfl

theorem eq_255 (h : IsUnit E) :
    (A.map (↑) + B.map (· • I))⁻¹ =
      (1 - t • I : ℂ) • ((E).map (↑) + (F).map (· • I))⁻¹ :=
  sorry

theorem eq_256 (h : IsUnit E)  :
    (A.map (↑) + B.map (· • I))⁻¹ =
      (1 - t • I : ℂ) • ((E + F * E⁻¹ * F)⁻¹.map (↑) - ((E + F * E⁻¹ * F)⁻¹ * F * E).map (· • I))⁻¹ := by
  rw [eq_255 _ _ h]
  sorry

theorem eq_257 (h : IsUnit E)  :
    (A.map (↑) + B.map (· • I))⁻¹ =
      (1 - t • I : ℂ) • ((E + F * E⁻¹ * F)⁻¹.map (↑) * (1 - (F * E⁻¹).map (· • I))) := by
  rw [eq_256 _ _ h]
  sorry

theorem eq_258 (h : IsUnit E) :
    (A.map (↑) + B.map (· • I))⁻¹ =
      (E + F * E⁻¹ * F)⁻¹.map (↑) *
        ((1 - t • (F * E⁻¹).map (↑)) - (t • 1 + (F * E⁻¹)).map (· • I)) := by
  rw [eq_257 _ _ h]
  sorry

theorem eq_259 (h : IsUnit E) :
    (A.map (↑) + B.map (· • I))⁻¹ =
      ((E + F * E⁻¹ * F)⁻¹ * (1 - t • (F * E⁻¹))).map (↑) -
       ((E + F * E⁻¹ * F)⁻¹ * (t • 1 + (F * E⁻¹))).map (· • I) := by
  rw [eq_258 _ _ h, mul_sub]
  sorry

end

end MatrixCookbook
