module

public import Mathlib.RingTheory.Complex

set_option doc.verso true

/-!
# Complex Matrices
-/

@[expose] public section

namespace MatrixCookbook

/--
> The complex scalar product $`r = pq` can be written as

  $$`\begin{bmatrix} \Re r \\ \Im r \end{bmatrix} = \begin{bmatrix} \Re p & -\Im p \\ \Im p & \Re p \end{bmatrix}\begin{bmatrix} \Re q \\ \Im q \end{bmatrix} \tag{225}`
-/
theorem eq_225 (z : ℂ) : Algebra.leftMulMatrix Complex.basisOneI z = !![z.re, -z.im; z.im, z.re] :=
  Algebra.leftMulMatrix_complex z

/-!
## Complex Derivatives
-/

/--
> In order to differentiate an expression $`f(z)` with respect to a complex $`z`, the Cauchy-Riemann equations have to be satisfied (\[7\]):

  $$`\frac{df(z)}{dz} = \frac{\partial\Re(f(z))}{\partial\Re z} + i\frac{\partial\Im(f(z))}{\partial\Re z} \tag{226}`
-/
theorem eq_226 : (sorry : Prop) :=
  sorry

/--
> and

  $$`\frac{df(z)}{dz} = -i\frac{\partial\Re(f(z))}{\partial\Im z} + \frac{\partial\Im(f(z))}{\partial\Im z} \tag{227}`
-/
theorem eq_227 : (sorry : Prop) :=
  sorry

/--
> or in a more compact form:

  $$`\frac{\partial f(z)}{\partial\Im z} = i\frac{\partial f(z)}{\partial\Re z}. \tag{228}`
-/
theorem eq_228 : (sorry : Prop) :=
  sorry

/-!
> A complex function that satisfies the Cauchy-Riemann equations for points in a region R is said yo be _analytic_ in this region R. In general, expressions involving complex conjugate or conjugate transpose do not satisfy the Cauchy-Riemann equations. In order to avoid this problem, a more generalized definition of complex derivative is used (\[24\], \[6\]):
-/

/--
> • Generalized Complex Derivative:

  $$`\frac{df(z)}{dz} = \frac{1}{2}\Big(\frac{\partial f(z)}{\partial\Re z} - i\frac{\partial f(z)}{\partial\Im z}\Big). \tag{229}`
-/
theorem eq_229 : (sorry : Prop) :=
  sorry

/--
> • Conjugate Complex Derivative

  $$`\frac{df(z)}{dz^*} = \frac{1}{2}\Big(\frac{\partial f(z)}{\partial\Re z} + i\frac{\partial f(z)}{\partial\Im z}\Big). \tag{230}`
-/
theorem eq_230 : (sorry : Prop) :=
  sorry

/-!
> The Generalized Complex Derivative equals the normal derivative, when $`f` is an analytic function. For a non-analytic function such as $`f(z) = z^*`, the derivative equals zero. The Conjugate Complex Derivative equals zero, when $`f` is an analytic function. The Conjugate Complex Derivative has e.g been used by \[21\] when deriving a complex gradient.
-/

/--
> Notice:

  $$`\frac{df(z)}{dz} \neq \frac{\partial f(z)}{\partial\Re z} + i\frac{\partial f(z)}{\partial\Im z}. \tag{231}`
-/
theorem eq_231 : (sorry : Prop) :=
  sorry

/--
> • Complex Gradient Vector: If $`f` is a real function of a complex vector $`\mathbf{z}`, then the complex gradient vector is given by (\[14, p. 798\])

  $$`\begin{aligned} \nabla f(\mathbf{z}) &= 2\frac{df(\mathbf{z})}{d\mathbf{z}^*} \\ &= \frac{\partial f(\mathbf{z})}{\partial\Re\mathbf{z}} + i\frac{\partial f(\mathbf{z})}{\partial\Im\mathbf{z}}. \end{aligned} \tag{232}`
-/
theorem eq_232 : (sorry : Prop) :=
  sorry

/--
> • Complex Gradient Matrix: If $`f` is a real function of a complex matrix $`\mathbf{Z}`, then the complex gradient matrix is given by (\[2\])

  $$`\begin{aligned} \nabla f(\mathbf{Z}) &= 2\frac{df(\mathbf{Z})}{d\mathbf{Z}^*} \\ &= \frac{\partial f(\mathbf{Z})}{\partial\Re\mathbf{Z}} + i\frac{\partial f(\mathbf{Z})}{\partial\Im\mathbf{Z}}. \end{aligned} \tag{233}`
-/
theorem eq_233 : (sorry : Prop) :=
  sorry

/-!
> These expressions can be used for gradient descent algorithms.

### The Chain Rule for complex numbers
-/

/--
> The chain rule is a little more complicated when the function of a complex $`u = f(x)` is non-analytic. For a non-analytic function, the following chain rule can be applied (\[7\])

  $$`\begin{aligned} \frac{\partial g(u)}{\partial x} &= \frac{\partial g}{\partial u}\frac{\partial u}{\partial x} + \frac{\partial g}{\partial u^*}\frac{\partial u^*}{\partial x} \\ &= \frac{\partial g}{\partial u}\frac{\partial u}{\partial x} + \Big(\frac{\partial g^*}{\partial u}\Big)^*\frac{\partial u^*}{\partial x} \end{aligned} \tag{234}`
-/
theorem eq_234 : (sorry : Prop) :=
  sorry

/--
> Notice, if the function is analytic, the second term reduces to zero, and the function is reduced to the normal well-known chain rule. For the matrix derivative of a scalar function $`g(\mathbf{U})`, the chain rule can be written the following way:

  $$`\frac{\partial g(\mathbf{U})}{\partial\mathbf{X}} = \frac{\operatorname{Tr}((\frac{\partial g(\mathbf{U})}{\partial\mathbf{U}})^T\partial\mathbf{U})}{\partial\mathbf{X}} + \frac{\operatorname{Tr}((\frac{\partial g(\mathbf{U})}{\partial\mathbf{U}^*})^T\partial\mathbf{U}^*)}{\partial\mathbf{X}}. \tag{235}`
-/
theorem eq_235 : (sorry : Prop) :=
  sorry

/-!
### Complex Derivatives of Traces
-/

/--
> If the derivatives involve complex numbers, the conjugate transpose is often involved. The most useful way to show complex derivative is to show the derivative with respect to the real and the imaginary part separately. An easy example is:

  $$`\frac{\partial\operatorname{Tr}(\mathbf{X}^*)}{\partial\Re\mathbf{X}} = \frac{\partial\operatorname{Tr}(\mathbf{X}^H)}{\partial\Re\mathbf{X}} = \mathbf{I} \tag{236}`
-/
theorem eq_236 : (sorry : Prop) :=
  sorry

/--
> $$`i\frac{\partial\operatorname{Tr}(\mathbf{X}^*)}{\partial\Im\mathbf{X}} = i\frac{\partial\operatorname{Tr}(\mathbf{X}^H)}{\partial\Im\mathbf{X}} = \mathbf{I} \tag{237}`
-/
theorem eq_237 : (sorry : Prop) :=
  sorry

/--
> Since the two results have the same sign, the conjugate complex derivative (230) should be used.

  $$`\frac{\partial\operatorname{Tr}(\mathbf{X})}{\partial\Re\mathbf{X}} = \frac{\partial\operatorname{Tr}(\mathbf{X}^T)}{\partial\Re\mathbf{X}} = \mathbf{I} \tag{238}`
-/
theorem eq_238 : (sorry : Prop) :=
  sorry

/--
> $$`i\frac{\partial\operatorname{Tr}(\mathbf{X})}{\partial\Im\mathbf{X}} = i\frac{\partial\operatorname{Tr}(\mathbf{X}^T)}{\partial\Im\mathbf{X}} = -\mathbf{I} \tag{239}`
-/
theorem eq_239 : (sorry : Prop) :=
  sorry

/--
> Here, the two results have different signs, and the generalized complex derivative (229) should be used. Hereby, it can be seen that (100) holds even if $`\mathbf{X}` is a complex number.

  $$`\frac{\partial\operatorname{Tr}(\mathbf{A}\mathbf{X}^H)}{\partial\Re\mathbf{X}} = \mathbf{A} \tag{240}`
-/
theorem eq_240 : (sorry : Prop) :=
  sorry

/--
> $$`i\frac{\partial\operatorname{Tr}(\mathbf{A}\mathbf{X}^H)}{\partial\Im\mathbf{X}} = \mathbf{A} \tag{241}`
-/
theorem eq_241 : (sorry : Prop) :=
  sorry

/--
> $$`\frac{\partial\operatorname{Tr}(\mathbf{A}\mathbf{X}^*)}{\partial\Re\mathbf{X}} = \mathbf{A}^T \tag{242}`
-/
theorem eq_242 : (sorry : Prop) :=
  sorry

/--
> $$`i\frac{\partial\operatorname{Tr}(\mathbf{A}\mathbf{X}^*)}{\partial\Im\mathbf{X}} = \mathbf{A}^T \tag{243}`
-/
theorem eq_243 : (sorry : Prop) :=
  sorry

/--
> $$`\frac{\partial\operatorname{Tr}(\mathbf{X}\mathbf{X}^H)}{\partial\Re\mathbf{X}} = \frac{\partial\operatorname{Tr}(\mathbf{X}^H\mathbf{X})}{\partial\Re\mathbf{X}} = 2\Re\mathbf{X} \tag{244}`
-/
theorem eq_244 : (sorry : Prop) :=
  sorry

/--
> $$`i\frac{\partial\operatorname{Tr}(\mathbf{X}\mathbf{X}^H)}{\partial\Im\mathbf{X}} = i\frac{\partial\operatorname{Tr}(\mathbf{X}^H\mathbf{X})}{\partial\Im\mathbf{X}} = i2\Im\mathbf{X} \tag{245}`
-/
theorem eq_245 : (sorry : Prop) :=
  sorry

/--
> By inserting (244) and (245) in (229) and (230), it can be seen that

  $$`\frac{\partial\operatorname{Tr}(\mathbf{X}\mathbf{X}^H)}{\partial\mathbf{X}} = \mathbf{X}^* \tag{246}`
-/
theorem eq_246 : (sorry : Prop) :=
  sorry

/--
> $$`\frac{\partial\operatorname{Tr}(\mathbf{X}\mathbf{X}^H)}{\partial\mathbf{X}^*} = \mathbf{X} \tag{247}`
-/
theorem eq_247 : (sorry : Prop) :=
  sorry

/--
> Since the function $`\operatorname{Tr}(\mathbf{X}\mathbf{X}^H)` is a real function of the complex matrix $`\mathbf{X}`, the complex gradient matrix (233) is given by

  $$`\nabla\operatorname{Tr}(\mathbf{X}\mathbf{X}^H) = 2\frac{\partial\operatorname{Tr}(\mathbf{X}\mathbf{X}^H)}{\partial\mathbf{X}^*} = 2\mathbf{X} \tag{248}`
-/
theorem eq_248 : (sorry : Prop) :=
  sorry

/-!
### Complex Derivative Involving Determinants
-/

/--
> Here, a calculation example is provided. The objective is to find the derivative of $`\det(\mathbf{X}^H\mathbf{A}\mathbf{X})` with respect to $`\mathbf{X}\in\mathbb{C}^{m\times n}`. The derivative is found with respect to the real part and the imaginary part of $`\mathbf{X}`, by use of (42) and (37), $`\det(\mathbf{X}^H\mathbf{A}\mathbf{X})` can be calculated as (see App. B.1.4 for details)

  $$`\begin{aligned} \frac{\partial\det(\mathbf{X}^H\mathbf{A}\mathbf{X})}{\partial\mathbf{X}} &= \frac{1}{2}\Big(\frac{\partial\det(\mathbf{X}^H\mathbf{A}\mathbf{X})}{\partial\Re\mathbf{X}} - i\frac{\partial\det(\mathbf{X}^H\mathbf{A}\mathbf{X})}{\partial\Im\mathbf{X}}\Big) \\ &= \det(\mathbf{X}^H\mathbf{A}\mathbf{X})\big((\mathbf{X}^H\mathbf{A}\mathbf{X})^{-1}\mathbf{X}^H\mathbf{A}\big)^T \end{aligned} \tag{249}`
-/
theorem eq_249 : (sorry : Prop) :=
  sorry

/--
> and the complex conjugate derivative yields

  $$`\begin{aligned} \frac{\partial\det(\mathbf{X}^H\mathbf{A}\mathbf{X})}{\partial\mathbf{X}^*} &= \frac{1}{2}\Big(\frac{\partial\det(\mathbf{X}^H\mathbf{A}\mathbf{X})}{\partial\Re\mathbf{X}} + i\frac{\partial\det(\mathbf{X}^H\mathbf{A}\mathbf{X})}{\partial\Im\mathbf{X}}\Big) \\ &= \det(\mathbf{X}^H\mathbf{A}\mathbf{X})\mathbf{A}\mathbf{X}(\mathbf{X}^H\mathbf{A}\mathbf{X})^{-1} \end{aligned} \tag{250}`
-/
theorem eq_250 : (sorry : Prop) :=
  sorry

/-!
## Higher order and non-linear derivatives
-/

/--
> $$`\frac{\partial}{\partial\mathbf{x}}\frac{(\mathbf{A}\mathbf{x})^H(\mathbf{A}\mathbf{x})}{(\mathbf{B}\mathbf{x})^H(\mathbf{B}\mathbf{x})} = \frac{\partial}{\partial\mathbf{x}}\frac{\mathbf{x}^H\mathbf{A}^H\mathbf{A}\mathbf{x}}{\mathbf{x}^H\mathbf{B}^H\mathbf{B}\mathbf{x}} \tag{251}`
-/
theorem eq_251 : (sorry : Prop) :=
  sorry

/--
> $$`= 2\frac{\mathbf{A}^H\mathbf{A}\mathbf{x}}{\mathbf{x}^H\mathbf{B}\mathbf{B}\mathbf{x}} - 2\frac{\mathbf{x}^H\mathbf{A}^H\mathbf{A}\mathbf{x}\mathbf{B}^H\mathbf{B}\mathbf{x}}{(\mathbf{x}^H\mathbf{B}^H\mathbf{B}\mathbf{x})^2} \tag{252}`
-/
theorem eq_252 : (sorry : Prop) :=
  sorry

section
variable [Fintype m] [DecidableEq m] (A B : Matrix m m ℝ) {t : ℝ}

local notation "E" => A + t • B
local notation "F" => B - t • A

open Complex (I)

/-!
## Inverse of complex sum
-/

/--
> Given real matrices $`\mathbf{A},\mathbf{B}` find the inverse of the complex sum $`\mathbf{A}+i\mathbf{B}`. Form the auxiliary matrices

  $$`\mathbf{E} = \mathbf{A}+t\mathbf{B} \tag{253}`
-/
theorem eq_253 : E = A + t • B := rfl

/--
> $$`\mathbf{F} = \mathbf{B}-t\mathbf{A}, \tag{254}`
-/
theorem eq_254 : F = B - t • A := rfl

/--
> and find a value of $`t` such that $`\mathbf{E}^{-1}` exists. Then

  $$`(\mathbf{A}+i\mathbf{B})^{-1} = (1-it)(\mathbf{E}+i\mathbf{F})^{-1} \tag{255}`
-/
theorem eq_255 (h : IsUnit E) :
    (A.map (↑) + B.map (· • I))⁻¹ =
      (1 - t • I : ℂ) • ((E).map (↑) + (F).map (· • I))⁻¹ :=
  sorry

/--
> $$`= (1-it)((\mathbf{E}+\mathbf{F}\mathbf{E}^{-1}\mathbf{F})^{-1} - i(\mathbf{E}+\mathbf{F}\mathbf{E}^{-1}\mathbf{F})^{-1}\mathbf{F}\mathbf{E}^{-1}) \tag{256}`
-/
theorem eq_256 (h : IsUnit E)  :
    (A.map (↑) + B.map (· • I))⁻¹ =
      (1 - t • I : ℂ) • ((E + F * E⁻¹ * F)⁻¹.map (↑) - ((E + F * E⁻¹ * F)⁻¹ * F * E).map (· • I))⁻¹ := by
  rw [eq_255 _ _ h]
  sorry

/--
> $$`= (1-it)(\mathbf{E}+\mathbf{F}\mathbf{E}^{-1}\mathbf{F})^{-1}(\mathbf{I}-i\mathbf{F}\mathbf{E}^{-1}) \tag{257}`
-/
theorem eq_257 (h : IsUnit E)  :
    (A.map (↑) + B.map (· • I))⁻¹ =
      (1 - t • I : ℂ) • ((E + F * E⁻¹ * F)⁻¹.map (↑) * (1 - (F * E⁻¹).map (· • I))) := by
  rw [eq_256 _ _ h]
  sorry

/--
> $$`= (\mathbf{E}+\mathbf{F}\mathbf{E}^{-1}\mathbf{F})^{-1}((\mathbf{I}-t\mathbf{F}\mathbf{E}^{-1}) - i(t\mathbf{I}+\mathbf{F}\mathbf{E}^{-1})) \tag{258}`
-/
theorem eq_258 (h : IsUnit E) :
    (A.map (↑) + B.map (· • I))⁻¹ =
      (E + F * E⁻¹ * F)⁻¹.map (↑) *
        ((1 - t • (F * E⁻¹).map (↑)) - (t • 1 + (F * E⁻¹)).map (· • I)) := by
  rw [eq_257 _ _ h]
  sorry

/--
> $$`\begin{aligned} &= (\mathbf{E}+\mathbf{F}\mathbf{E}^{-1}\mathbf{F})^{-1}(\mathbf{I}-t\mathbf{F}\mathbf{E}^{-1}) \\ &\quad -i(\mathbf{E}+\mathbf{F}\mathbf{E}^{-1}\mathbf{F})^{-1}(t\mathbf{I}+\mathbf{F}\mathbf{E}^{-1}) \end{aligned} \tag{259}`
-/
theorem eq_259 (h : IsUnit E) :
    (A.map (↑) + B.map (· • I))⁻¹ =
      ((E + F * E⁻¹ * F)⁻¹ * (1 - t • (F * E⁻¹))).map (↑) -
       ((E + F * E⁻¹ * F)⁻¹ * (t • 1 + (F * E⁻¹))).map (· • I) := by
  rw [eq_258 _ _ h, mul_sub]
  sorry

end

end MatrixCookbook
