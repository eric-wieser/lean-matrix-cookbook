module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Analysis.Normed.Field.Basic
public import MatrixCookbook.ForMathlib.Analysis.Matrix

set_option doc.verso true

/-!
# Derivatives

> This section is covering differentiation of a number of expressions with respect to a matrix $`\mathbf{X}`. Note that it is always assumed that $`\mathbf{X}` has _no special structure_, i.e. that the elements of $`\mathbf{X}` are independent (e.g. not symmetric, Toeplitz, positive definite). See section 2.8 for differentiation of structured matrices. The basic assumptions can be written in a formula as

  $$`\frac{\partial X_{kl}}{\partial X_{ij}} = \delta_{ik}\delta_{lj} \tag{32}`

  that is for e.g. vector forms,

  $$`\left[\frac{\partial \mathbf{x}}{\partial y}\right]_i = \frac{\partial x_i}{\partial y} \qquad \left[\frac{\partial x}{\partial \mathbf{y}}\right]_i = \frac{\partial x}{\partial y_i} \qquad \left[\frac{\partial \mathbf{x}}{\partial \mathbf{y}}\right]_{ij} = \frac{\partial x_i}{\partial y_j}`
-/

@[expose] public section

variable {ι : Type _} {R : Type _} {m n p q : Type _}

variable [Fintype m] [Fintype n] [Fintype p] [Fintype q]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

namespace MatrixCookbook

variable [NontriviallyNormedField R]

open scoped Matrix Kronecker

open Matrix

/-! TODO: is this what is actually meant by `∂(XY) = (∂X)Y + X(∂Y)`? -/

/--
> The following rules are general and very useful when deriving the differential of an expression (\[19\]):

  $$`\partial\mathbf{A} = 0 \qquad (\mathbf{A} \text{ is a constant}) \tag{33}`
-/
theorem eq_33 (A : Matrix m n R) : (deriv fun _ : R => A) = 0 :=
  open scoped Matrix.Norms.Elementwise in
  deriv_const' _

/--
> $$`\partial(\alpha\mathbf{X}) = \alpha\partial\mathbf{X} \tag{34}`
-/
theorem eq_34 (c : R) (X : R → Matrix m n R) (hX : Differentiable R X) :
    deriv (c • X) = c • deriv X :=
  open scoped Matrix.Norms.Elementwise in
  funext fun _ => deriv_const_smul c (hX _)

/--
> $$`\partial(\mathbf{X}+\mathbf{Y}) = \partial\mathbf{X} + \partial\mathbf{Y} \tag{35}`
-/
theorem eq_35 (X Y : R → Matrix m n R) (hX : Differentiable R X) (hY : Differentiable R Y) :
    deriv (X + Y) = deriv X + deriv Y :=
  open scoped Matrix.Norms.Elementwise in
  funext fun _ => deriv_add (hX _) (hY _)

/--
> $$`\partial(\operatorname{Tr}(\mathbf{X})) = \operatorname{Tr}(\partial\mathbf{X}) \tag{36}`
-/
theorem eq_36 (X : R → Matrix m m R) (hX : Differentiable R X) :
    (deriv fun a => trace (X a)) = fun a => trace (deriv X a) :=
  open scoped Matrix.Norms.Elementwise in
  funext fun _ => (hX _).hasDerivAt.trace.deriv

/--
> $$`\partial(\mathbf{X}\mathbf{Y}) = (\partial\mathbf{X})\mathbf{Y} + \mathbf{X}(\partial\mathbf{Y}) \tag{37}`
-/
theorem eq_37 (X : R → Matrix m n R) (Y : R → Matrix n p R) (hX : Differentiable R X)
    (hY : Differentiable R Y) :
    (deriv fun a => X a * Y a) = fun a => deriv X a * Y a + X a * deriv Y a :=
  open scoped Matrix.Norms.Elementwise in
  funext fun a => ((hX a).hasDerivAt.matrix_mul (hY a).hasDerivAt).deriv

/--
> $$`\partial(\mathbf{X}\circ\mathbf{Y}) = (\partial\mathbf{X})\circ\mathbf{Y} + \mathbf{X}\circ(\partial\mathbf{Y}) \tag{38}`
-/
theorem eq_38 (X Y : R → Matrix n p R) (hX : Differentiable R X) (hY : Differentiable R Y) :
    (deriv fun a => X a ⊙ Y a) = fun a => deriv X a ⊙ Y a + X a ⊙ deriv Y a :=
  open scoped Matrix.Norms.Elementwise in
  funext fun a => ((hX a).hasDerivAt.matrix_hadamard (hY a).hasDerivAt).deriv

/--
> $$`\partial(\mathbf{X}\otimes\mathbf{Y}) = (\partial\mathbf{X})\otimes\mathbf{Y} + \mathbf{X}\otimes(\partial\mathbf{Y}) \tag{39}`
-/
theorem eq_39 (X : R → Matrix m n R) (Y : R → Matrix p q R) (hX : Differentiable R X)
    (hY : Differentiable R Y) :
    (deriv fun a => X a ⊗ₖ Y a) = fun a => deriv X a ⊗ₖ Y a + X a ⊗ₖ deriv Y a :=
  open scoped Matrix.Norms.Elementwise in
  funext fun a => ((hX a).hasDerivAt.matrix_kronecker (hY a).hasDerivAt).deriv

/--
> $$`\partial(\mathbf{X}^{-1}) = -\mathbf{X}^{-1}(\partial\mathbf{X})\mathbf{X}^{-1} \tag{40}`
-/
theorem eq_40 [CompleteSpace R] (X : R → Matrix n n R) (hX : Differentiable R X)
    (hX' : ∀ a, IsUnit (X a)) :
    (deriv fun a => (X a)⁻¹) = fun a => -(X a)⁻¹ * deriv X a * (X a)⁻¹ :=
  open scoped Matrix.Norms.Operator in
  funext fun a => ((hX a).hasDerivAt.matrix_inv (hX' a)).deriv

/--
> $$`\partial(\det(\mathbf{X})) = \operatorname{Tr}(\operatorname{adj}(\mathbf{X})\partial\mathbf{X}) \tag{41}`
-/
theorem eq_41 (X : R → Matrix n n R) (hX : Differentiable R X) :
    (deriv fun a => det (X a)) = fun a => trace (adjugate (X a) * deriv X a) :=
  sorry

/--
> $$`\partial(\det(\mathbf{X})) = \det(\mathbf{X})\operatorname{Tr}(\mathbf{X}^{-1}\partial\mathbf{X}) \tag{42}`
-/
theorem eq_42 (X : R → Matrix n n R) (hX : Differentiable R X) :
    (deriv fun a => det (X a)) = fun a => det (X a) • trace ((X a)⁻¹ * deriv X a) :=
  sorry

/--
> $$`\partial(\ln(\det(\mathbf{X}))) = \operatorname{Tr}(\mathbf{X}^{-1}\partial\mathbf{X}) \tag{43}`
-/
theorem eq_43 (X : ℝ → Matrix n n ℝ) (hX : Differentiable ℝ X) :
    (deriv fun a => Real.log (det (X a))) = fun a => trace ((X a)⁻¹ * deriv X a) :=
  sorry

/--
> $$`\partial\mathbf{X}^T = (\partial\mathbf{X})^T \tag{44}`
-/
theorem eq_44 (X : R → Matrix m n R) (hX : Differentiable R X) :
    (deriv fun a => (X a)ᵀ) = fun a => (deriv X a)ᵀ :=
  open scoped Matrix.Norms.Elementwise in
  funext fun _ => (hX _).hasDerivAt.transpose.deriv

/--
> $$`\partial\mathbf{X}^H = (\partial\mathbf{X})^H \tag{45}`
-/
theorem eq_45 (X : ℝ → Matrix m n ℂ) (hX : Differentiable ℝ X) :
    (deriv fun a => (X a)ᴴ) = fun a => (deriv X a)ᴴ :=
  open scoped Matrix.Norms.Elementwise in
  funext fun _ => (hX _).hasDerivAt.conjTranspose.deriv

/-!
## Derivatives of a Determinant

### General form
-/

/--
> $$`\frac{\partial\det(\mathbf{Y})}{\partial x} = \det(\mathbf{Y})\operatorname{Tr}\left[\mathbf{Y}^{-1}\frac{\partial\mathbf{Y}}{\partial x}\right] \tag{46}`
-/
theorem eq_46 (X : R → Matrix n n R) (hX : Differentiable R X) :
    (deriv fun a => det (X a)) = fun a => det (X a) • trace ((X a)⁻¹ * deriv X a) :=
  -- this suggests we might have 42 stated strangely
  eq_42 X hX

/-!
> $$`\sum_k \frac{\partial\det(\mathbf{X})}{\partial X_{ik}} X_{jk} = \delta_{ij}\det(\mathbf{X}) \tag{47}`

  $$`\begin{aligned} \frac{\partial^2\det(\mathbf{Y})}{\partial x^2} &= \det(\mathbf{Y})\left[\operatorname{Tr}\left[\mathbf{Y}^{-1}\frac{\partial\frac{\partial\mathbf{Y}}{\partial x}}{\partial x}\right]\right. \\ &\qquad +\operatorname{Tr}\left[\mathbf{Y}^{-1}\frac{\partial\mathbf{Y}}{\partial x}\right]\operatorname{Tr}\left[\mathbf{Y}^{-1}\frac{\partial\mathbf{Y}}{\partial x}\right] \\ &\qquad \left.-\operatorname{Tr}\left[\left(\mathbf{Y}^{-1}\frac{\partial\mathbf{Y}}{\partial x}\right)\left(\mathbf{Y}^{-1}\frac{\partial\mathbf{Y}}{\partial x}\right)\right]\right] \end{aligned} \tag{48}`

### Linear forms

> $$`\frac{\partial\det(\mathbf{X})}{\partial\mathbf{X}} = \det(\mathbf{X})(\mathbf{X}^{-1})^T \tag{49}`

  $$`\sum_k \frac{\partial\det(\mathbf{X})}{\partial X_{ik}} X_{jk} = \delta_{ij}\det(\mathbf{X}) \tag{50}`

  $$`\frac{\partial\det(\mathbf{A}\mathbf{X}\mathbf{B})}{\partial\mathbf{X}} = \det(\mathbf{A}\mathbf{X}\mathbf{B})(\mathbf{X}^{-1})^T = \det(\mathbf{A}\mathbf{X}\mathbf{B})(\mathbf{X}^T)^{-1} \tag{51}`

### Square forms

> If $`\mathbf{X}` is square and invertible, then

  $$`\frac{\partial\det(\mathbf{X}^T\mathbf{A}\mathbf{X})}{\partial\mathbf{X}} = 2\det(\mathbf{X}^T\mathbf{A}\mathbf{X})\mathbf{X}^{-T} \tag{52}`

  If $`\mathbf{X}` is not square but $`\mathbf{A}` is symmetric, then

  $$`\frac{\partial\det(\mathbf{X}^T\mathbf{A}\mathbf{X})}{\partial\mathbf{X}} = 2\det(\mathbf{X}^T\mathbf{A}\mathbf{X})\mathbf{A}\mathbf{X}(\mathbf{X}^T\mathbf{A}\mathbf{X})^{-1} \tag{53}`

  If $`\mathbf{X}` is not square and $`\mathbf{A}` is not symmetric, then

  $$`\frac{\partial\det(\mathbf{X}^T\mathbf{A}\mathbf{X})}{\partial\mathbf{X}} = \det(\mathbf{X}^T\mathbf{A}\mathbf{X})(\mathbf{A}\mathbf{X}(\mathbf{X}^T\mathbf{A}\mathbf{X})^{-1} + \mathbf{A}^T\mathbf{X}(\mathbf{X}^T\mathbf{A}^T\mathbf{X})^{-1}) \tag{54}`

### Other nonlinear forms

> Some special cases are (See \[9, 7\])

  $$`\frac{\partial\ln\det(\mathbf{X}^T\mathbf{X})|}{\partial\mathbf{X}} = 2(\mathbf{X}^+)^T \tag{55}`

  $$`\frac{\partial\ln\det(\mathbf{X}^T\mathbf{X})}{\partial\mathbf{X}^+} = -2\mathbf{X}^T \tag{56}`

  $$`\frac{\partial\ln|\det(\mathbf{X})|}{\partial\mathbf{X}} = (\mathbf{X}^{-1})^T = (\mathbf{X}^T)^{-1} \tag{57}`

  $$`\frac{\partial\det(\mathbf{X}^k)}{\partial\mathbf{X}} = k\det(\mathbf{X}^k)\mathbf{X}^{-T} \tag{58}`

## Derivatives of an Inverse

> From \[27\] we have the basic identity

  $$`\frac{\partial\mathbf{Y}^{-1}}{\partial x} = -\mathbf{Y}^{-1}\frac{\partial\mathbf{Y}}{\partial x}\mathbf{Y}^{-1} \tag{59}`

  from which it follows

  $$`\frac{\partial(\mathbf{X}^{-1})_{kl}}{\partial X_{ij}} = -(\mathbf{X}^{-1})_{ki}(\mathbf{X}^{-1})_{jl} \tag{60}`

  $$`\frac{\partial\mathbf{a}^T\mathbf{X}^{-1}\mathbf{b}}{\partial\mathbf{X}} = -\mathbf{X}^{-T}\mathbf{a}\mathbf{b}^T\mathbf{X}^{-T} \tag{61}`

  $$`\frac{\partial\det(\mathbf{X}^{-1})}{\partial\mathbf{X}} = -\det(\mathbf{X}^{-1})(\mathbf{X}^{-1})^T \tag{62}`

  $$`\frac{\partial\operatorname{Tr}(\mathbf{A}\mathbf{X}^{-1}\mathbf{B})}{\partial\mathbf{X}} = -(\mathbf{X}^{-1}\mathbf{B}\mathbf{A}\mathbf{X}^{-1})^T \tag{63}`

  $$`\frac{\partial\operatorname{Tr}((\mathbf{X}+\mathbf{A})^{-1})}{\partial\mathbf{X}} = -((\mathbf{X}+\mathbf{A})^{-1}(\mathbf{X}+\mathbf{A})^{-1})^T \tag{64}`

  From \[32\] we have the following result: Let $`\mathbf{A}` be an $`n\times n` invertible square matrix, $`\mathbf{W}` be the inverse of $`\mathbf{A}`, and $`J(\mathbf{A})` is an $`n\times n` -variate and differentiable function with respect to $`\mathbf{A}`, then the partial differentials of $`J` with respect to $`\mathbf{A}` and $`\mathbf{W}` satisfy

  $$`\frac{\partial J}{\partial\mathbf{A}} = -\mathbf{A}^{-T}\frac{\partial J}{\partial\mathbf{W}}\mathbf{A}^{-T}`

## Derivatives of Eigenvalues

> $$`\frac{\partial}{\partial\mathbf{X}}\sum\operatorname{eig}(\mathbf{X}) = \frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{X}) = \mathbf{I} \tag{65}`

  $$`\frac{\partial}{\partial\mathbf{X}}\prod\operatorname{eig}(\mathbf{X}) = \frac{\partial}{\partial\mathbf{X}}\det(\mathbf{X}) = \det(\mathbf{X})\mathbf{X}^{-T} \tag{66}`

  If $`\mathbf{A}` is real and symmetric, $`\lambda_i` and $`\mathbf{v}_i` are distinct eigenvalues and eigenvectors of $`\mathbf{A}` (see (276)) with $`\mathbf{v}_i^T\mathbf{v}_i = 1`, then \[33\]

  $$`\partial\lambda_i = \mathbf{v}_i^T\partial(\mathbf{A})\mathbf{v}_i \tag{67}`

  $$`\partial\mathbf{v}_i = (\lambda_i\mathbf{I} - \mathbf{A})^+\partial(\mathbf{A})\mathbf{v}_i \tag{68}`

## Derivatives of Matrices, Vectors and Scalar Forms

### First Order

> $$`\frac{\partial\mathbf{x}^T\mathbf{a}}{\partial\mathbf{x}} = \frac{\partial\mathbf{a}^T\mathbf{x}}{\partial\mathbf{x}} = \mathbf{a} \tag{69}`

  $$`\frac{\partial\mathbf{a}^T\mathbf{X}\mathbf{b}}{\partial\mathbf{X}} = \mathbf{a}\mathbf{b}^T \tag{70}`

  $$`\frac{\partial\mathbf{a}^T\mathbf{X}^T\mathbf{b}}{\partial\mathbf{X}} = \mathbf{b}\mathbf{a}^T \tag{71}`

  $$`\frac{\partial\mathbf{a}^T\mathbf{X}\mathbf{a}}{\partial\mathbf{X}} = \frac{\partial\mathbf{a}^T\mathbf{X}^T\mathbf{a}}{\partial\mathbf{X}} = \mathbf{a}\mathbf{a}^T \tag{72}`

  $$`\frac{\partial\mathbf{X}}{\partial X_{ij}} = \mathbf{J}^{ij} \tag{73}`

  $$`\frac{\partial(\mathbf{X}\mathbf{A})_{ij}}{\partial X_{mn}} = \delta_{im}(\mathbf{A})_{nj} = (\mathbf{J}^{mn}\mathbf{A})_{ij} \tag{74}`

  $$`\frac{\partial(\mathbf{X}^T\mathbf{A})_{ij}}{\partial X_{mn}} = \delta_{in}(\mathbf{A})_{mj} = (\mathbf{J}^{nm}\mathbf{A})_{ij} \tag{75}`

### Second Order

> $$`\frac{\partial}{\partial X_{ij}}\sum_{klmn} X_{kl}X_{mn} = 2\sum_{kl} X_{kl} \tag{76}`

  $$`\frac{\partial\mathbf{b}^T\mathbf{X}^T\mathbf{X}\mathbf{c}}{\partial\mathbf{X}} = \mathbf{X}(\mathbf{b}\mathbf{c}^T + \mathbf{c}\mathbf{b}^T) \tag{77}`

  $$`\frac{\partial(\mathbf{B}\mathbf{x}+\mathbf{b})^T\mathbf{C}(\mathbf{D}\mathbf{x}+\mathbf{d})}{\partial\mathbf{x}} = \mathbf{B}^T\mathbf{C}(\mathbf{D}\mathbf{x}+\mathbf{d}) + \mathbf{D}^T\mathbf{C}^T(\mathbf{B}\mathbf{x}+\mathbf{b}) \tag{78}`

  $$`\frac{\partial(\mathbf{X}^T\mathbf{B}\mathbf{X})_{kl}}{\partial X_{ij}} = \delta_{lj}(\mathbf{X}^T\mathbf{B})_{ki} + \delta_{kj}(\mathbf{B}\mathbf{X})_{il} \tag{79}`

  $$`\frac{\partial(\mathbf{X}^T\mathbf{B}\mathbf{X})}{\partial X_{ij}} = \mathbf{X}^T\mathbf{B}\mathbf{J}^{ij} + \mathbf{J}^{ji}\mathbf{B}\mathbf{X} \qquad (\mathbf{J}^{ij})_{kl} = \delta_{ik}\delta_{jl} \tag{80}`

  See Sec 9.7 for useful properties of the Single-entry matrix $`\mathbf{J}^{ij}`

  $$`\frac{\partial\mathbf{x}^T\mathbf{B}\mathbf{x}}{\partial\mathbf{x}} = (\mathbf{B}+\mathbf{B}^T)\mathbf{x} \tag{81}`

  $$`\frac{\partial\mathbf{b}^T\mathbf{X}^T\mathbf{D}\mathbf{X}\mathbf{c}}{\partial\mathbf{X}} = \mathbf{D}^T\mathbf{X}\mathbf{b}\mathbf{c}^T + \mathbf{D}\mathbf{X}\mathbf{c}\mathbf{b}^T \tag{82}`

  $$`\frac{\partial}{\partial\mathbf{X}}(\mathbf{X}\mathbf{b}+\mathbf{c})^T\mathbf{D}(\mathbf{X}\mathbf{b}+\mathbf{c}) = (\mathbf{D}+\mathbf{D}^T)(\mathbf{X}\mathbf{b}+\mathbf{c})\mathbf{b}^T \tag{83}`

  Assume $`\mathbf{W}` is symmetric, then

  $$`\frac{\partial}{\partial\mathbf{s}}(\mathbf{x}-\mathbf{A}\mathbf{s})^T\mathbf{W}(\mathbf{x}-\mathbf{A}\mathbf{s}) = -2\mathbf{A}^T\mathbf{W}(\mathbf{x}-\mathbf{A}\mathbf{s}) \tag{84}`

  $$`\frac{\partial}{\partial\mathbf{x}}(\mathbf{x}-\mathbf{s})^T\mathbf{W}(\mathbf{x}-\mathbf{s}) = 2\mathbf{W}(\mathbf{x}-\mathbf{s}) \tag{85}`

  $$`\frac{\partial}{\partial\mathbf{s}}(\mathbf{x}-\mathbf{s})^T\mathbf{W}(\mathbf{x}-\mathbf{s}) = -2\mathbf{W}(\mathbf{x}-\mathbf{s}) \tag{86}`

  $$`\frac{\partial}{\partial\mathbf{x}}(\mathbf{x}-\mathbf{A}\mathbf{s})^T\mathbf{W}(\mathbf{x}-\mathbf{A}\mathbf{s}) = 2\mathbf{W}(\mathbf{x}-\mathbf{A}\mathbf{s}) \tag{87}`

  $$`\frac{\partial}{\partial\mathbf{A}}(\mathbf{x}-\mathbf{A}\mathbf{s})^T\mathbf{W}(\mathbf{x}-\mathbf{A}\mathbf{s}) = -2\mathbf{W}(\mathbf{x}-\mathbf{A}\mathbf{s})\mathbf{s}^T \tag{88}`

  As a case with complex values the following holds

  $$`\frac{\partial(a-\mathbf{x}^H\mathbf{b})^2}{\partial\mathbf{x}} = -2\mathbf{b}(a-\mathbf{x}^H\mathbf{b})^* \tag{89}`

  This formula is also known from the LMS algorithm \[14\]

### Higher-order and non-linear

> $$`\frac{\partial(\mathbf{X}^n)_{kl}}{\partial X_{ij}} = \sum_{r=0}^{n-1}(\mathbf{X}^r\mathbf{J}^{ij}\mathbf{X}^{n-1-r})_{kl} \tag{90}`

  For proof of the above, see B.1.3.

  $$`\frac{\partial}{\partial\mathbf{X}}\mathbf{a}^T\mathbf{X}^n\mathbf{b} = \sum_{r=0}^{n-1}(\mathbf{X}^r)^T\mathbf{a}\mathbf{b}^T(\mathbf{X}^{n-1-r})^T \tag{91}`

  $$`\begin{aligned} \frac{\partial}{\partial\mathbf{X}}\mathbf{a}^T(\mathbf{X}^n)^T\mathbf{X}^n\mathbf{b} &= \sum_{r=0}^{n-1}\Big[\mathbf{X}^{n-1-r}\mathbf{a}\mathbf{b}^T(\mathbf{X}^n)^T\mathbf{X}^r \\ &\qquad + (\mathbf{X}^r)^T\mathbf{X}^n\mathbf{a}\mathbf{b}^T(\mathbf{X}^{n-1-r})^T\Big] \end{aligned} \tag{92}`

  See B.1.3 for a proof.

  Assume $`\mathbf{s}` and $`\mathbf{r}` are functions of $`\mathbf{x}`, i.e. $`\mathbf{s} = \mathbf{s}(\mathbf{x}), \mathbf{r} = \mathbf{r}(\mathbf{x})`, and that $`\mathbf{A}` is a constant, then

  $$`\frac{\partial}{\partial\mathbf{x}}\mathbf{s}^T\mathbf{A}\mathbf{r} = \left[\frac{\partial\mathbf{s}}{\partial\mathbf{x}}\right]^T\mathbf{A}\mathbf{r} + \left[\frac{\partial\mathbf{r}}{\partial\mathbf{x}}\right]^T\mathbf{A}^T\mathbf{s} \tag{93}`

  $$`\frac{\partial}{\partial\mathbf{x}}\frac{(\mathbf{A}\mathbf{x})^T(\mathbf{A}\mathbf{x})}{(\mathbf{B}\mathbf{x})^T(\mathbf{B}\mathbf{x})} = \frac{\partial}{\partial\mathbf{x}}\frac{\mathbf{x}^T\mathbf{A}^T\mathbf{A}\mathbf{x}}{\mathbf{x}^T\mathbf{B}^T\mathbf{B}\mathbf{x}} \tag{94}`

  $$`= 2\frac{\mathbf{A}^T\mathbf{A}\mathbf{x}}{\mathbf{x}^T\mathbf{B}\mathbf{B}\mathbf{x}} - 2\frac{\mathbf{x}^T\mathbf{A}^T\mathbf{A}\mathbf{x}\mathbf{B}^T\mathbf{B}\mathbf{x}}{(\mathbf{x}^T\mathbf{B}^T\mathbf{B}\mathbf{x})^2} \tag{95}`

### Gradient and Hessian

> Using the above we have for the gradient and the Hessian

  $$`f = \mathbf{x}^T\mathbf{A}\mathbf{x} + \mathbf{b}^T\mathbf{x} \tag{96}`

  $$`\nabla_{\mathbf{x}}f = \frac{\partial f}{\partial\mathbf{x}} = (\mathbf{A}+\mathbf{A}^T)\mathbf{x} + \mathbf{b} \tag{97}`

  $$`\frac{\partial^2 f}{\partial\mathbf{x}\partial\mathbf{x}^T} = \mathbf{A} + \mathbf{A}^T \tag{98}`

## Derivatives of Traces

> Assume $`F(\mathbf{X})` to be a differentiable function of each of the elements of $`X`. It then holds that

  $$`\frac{\partial\operatorname{Tr}(F(\mathbf{X}))}{\partial\mathbf{X}} = f(\mathbf{X})^T`

  where $`f(\cdot)` is the scalar derivative of $`F(\cdot)`.

### First Order

> $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{X}) = \mathbf{I} \tag{99}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{X}\mathbf{A}) = \mathbf{A}^T \tag{100}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{A}\mathbf{X}\mathbf{B}) = \mathbf{A}^T\mathbf{B}^T \tag{101}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{A}\mathbf{X}^T\mathbf{B}) = \mathbf{B}\mathbf{A} \tag{102}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{X}^T\mathbf{A}) = \mathbf{A} \tag{103}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{A}\mathbf{X}^T) = \mathbf{A} \tag{104}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{A}\otimes\mathbf{X}) = \operatorname{Tr}(\mathbf{A})\mathbf{I} \tag{105}`

### Second Order

> $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{X}^2) = 2\mathbf{X}^T \tag{106}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{X}^2\mathbf{B}) = (\mathbf{X}\mathbf{B}+\mathbf{B}\mathbf{X})^T \tag{107}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{X}^T\mathbf{B}\mathbf{X}) = \mathbf{B}\mathbf{X} + \mathbf{B}^T\mathbf{X} \tag{108}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{B}\mathbf{X}\mathbf{X}^T) = \mathbf{B}\mathbf{X} + \mathbf{B}^T\mathbf{X} \tag{109}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{X}\mathbf{X}^T\mathbf{B}) = \mathbf{B}\mathbf{X} + \mathbf{B}^T\mathbf{X} \tag{110}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{X}\mathbf{B}\mathbf{X}^T) = \mathbf{X}\mathbf{B}^T + \mathbf{X}\mathbf{B} \tag{111}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{B}\mathbf{X}^T\mathbf{X}) = \mathbf{X}\mathbf{B}^T + \mathbf{X}\mathbf{B} \tag{112}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{X}^T\mathbf{X}\mathbf{B}) = \mathbf{X}\mathbf{B}^T + \mathbf{X}\mathbf{B} \tag{113}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{A}\mathbf{X}\mathbf{B}\mathbf{X}) = \mathbf{A}^T\mathbf{X}^T\mathbf{B}^T + \mathbf{B}^T\mathbf{X}^T\mathbf{A}^T \tag{114}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{X}^T\mathbf{X}) = \frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{X}\mathbf{X}^T) = 2\mathbf{X} \tag{115}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{B}^T\mathbf{X}^T\mathbf{C}\mathbf{X}\mathbf{B}) = \mathbf{C}^T\mathbf{X}\mathbf{B}\mathbf{B}^T + \mathbf{C}\mathbf{X}\mathbf{B}\mathbf{B}^T \tag{116}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}\left[\mathbf{X}^T\mathbf{B}\mathbf{X}\mathbf{C}\right] = \mathbf{B}\mathbf{X}\mathbf{C} + \mathbf{B}^T\mathbf{X}\mathbf{C}^T \tag{117}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{A}\mathbf{X}\mathbf{B}\mathbf{X}^T\mathbf{C}) = \mathbf{A}^T\mathbf{C}^T\mathbf{X}\mathbf{B}^T + \mathbf{C}\mathbf{A}\mathbf{X}\mathbf{B} \tag{118}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}\Big[(\mathbf{A}\mathbf{X}\mathbf{B}+\mathbf{C})(\mathbf{A}\mathbf{X}\mathbf{B}+\mathbf{C})^T\Big] = 2\mathbf{A}^T(\mathbf{A}\mathbf{X}\mathbf{B}+\mathbf{C})\mathbf{B}^T \tag{119}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{X}\otimes\mathbf{X}) = \frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{X})\operatorname{Tr}(\mathbf{X}) = 2\operatorname{Tr}(\mathbf{X})\mathbf{I} \tag{120}`

  See \[7\].

### Higher Order

> $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{X}^k) = k(\mathbf{X}^{k-1})^T \tag{121}`

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{A}\mathbf{X}^k) = \sum_{r=0}^{k-1}(\mathbf{X}^r\mathbf{A}\mathbf{X}^{k-r-1})^T \tag{122}`

  $$`\begin{aligned} \frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}\left[\mathbf{B}^T\mathbf{X}^T\mathbf{C}\mathbf{X}\mathbf{X}^T\mathbf{C}\mathbf{X}\mathbf{B}\right] &= \mathbf{C}\mathbf{X}\mathbf{X}^T\mathbf{C}\mathbf{X}\mathbf{B}\mathbf{B}^T \\ &\quad + \mathbf{C}^T\mathbf{X}\mathbf{B}\mathbf{B}^T\mathbf{X}^T\mathbf{C}^T\mathbf{X} \\ &\quad + \mathbf{C}\mathbf{X}\mathbf{B}\mathbf{B}^T\mathbf{X}^T\mathbf{C}\mathbf{X} \\ &\quad + \mathbf{C}^T\mathbf{X}\mathbf{X}^T\mathbf{C}^T\mathbf{X}\mathbf{B}\mathbf{B}^T \end{aligned} \tag{123}`

### Other

> $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{A}\mathbf{X}^{-1}\mathbf{B}) = -(\mathbf{X}^{-1}\mathbf{B}\mathbf{A}\mathbf{X}^{-1})^T = -\mathbf{X}^{-T}\mathbf{A}^T\mathbf{B}^T\mathbf{X}^{-T} \tag{124}`

  Assume $`\mathbf{B}` and $`\mathbf{C}` to be symmetric, then

  $$`\frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}\Big[(\mathbf{X}^T\mathbf{C}\mathbf{X})^{-1}\mathbf{A}\Big] = -(\mathbf{C}\mathbf{X}(\mathbf{X}^T\mathbf{C}\mathbf{X})^{-1})(\mathbf{A}+\mathbf{A}^T)(\mathbf{X}^T\mathbf{C}\mathbf{X})^{-1} \tag{125}`

  $$`\begin{aligned} \frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}\Big[(\mathbf{X}^T\mathbf{C}\mathbf{X})^{-1}(\mathbf{X}^T\mathbf{B}\mathbf{X})\Big] &= -2\mathbf{C}\mathbf{X}(\mathbf{X}^T\mathbf{C}\mathbf{X})^{-1}\mathbf{X}^T\mathbf{B}\mathbf{X}(\mathbf{X}^T\mathbf{C}\mathbf{X})^{-1} \\ &\quad + 2\mathbf{B}\mathbf{X}(\mathbf{X}^T\mathbf{C}\mathbf{X})^{-1} \end{aligned} \tag{126}`

  $$`\begin{aligned} \frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}\Big[(\mathbf{A}+\mathbf{X}^T\mathbf{C}\mathbf{X})^{-1}(\mathbf{X}^T\mathbf{B}\mathbf{X})\Big] &= -2\mathbf{C}\mathbf{X}(\mathbf{A}+\mathbf{X}^T\mathbf{C}\mathbf{X})^{-1}\mathbf{X}^T\mathbf{B}\mathbf{X}(\mathbf{A}+\mathbf{X}^T\mathbf{C}\mathbf{X})^{-1} \\ &\quad + 2\mathbf{B}\mathbf{X}(\mathbf{A}+\mathbf{X}^T\mathbf{C}\mathbf{X})^{-1} \end{aligned} \tag{127}`

  See \[7\].

  $$`\frac{\partial\operatorname{Tr}(\sin(\mathbf{X}))}{\partial\mathbf{X}} = \cos(\mathbf{X})^T \tag{128}`

## Derivatives of vector norms

### Two-norm

> $$`\frac{\partial}{\partial\mathbf{x}}||\mathbf{x}-\mathbf{a}||_2 = \frac{\mathbf{x}-\mathbf{a}}{||\mathbf{x}-\mathbf{a}||_2} \tag{129}`

  $$`\frac{\partial}{\partial\mathbf{x}}\frac{\mathbf{x}-\mathbf{a}}{\|\mathbf{x}-\mathbf{a}\|_2} = \frac{\mathbf{I}}{\|\mathbf{x}-\mathbf{a}\|_2} - \frac{(\mathbf{x}-\mathbf{a})(\mathbf{x}-\mathbf{a})^T}{\|\mathbf{x}-\mathbf{a}\|_2^3} \tag{130}`

  $$`\frac{\partial||\mathbf{x}||_2^2}{\partial\mathbf{x}} = \frac{\partial||\mathbf{x}^T\mathbf{x}||_2}{\partial\mathbf{x}} = 2\mathbf{x} \tag{131}`

## Derivatives of matrix norms

> For more on matrix norms, see Sec. 10.4.

### Frobenius norm

> $$`\frac{\partial}{\partial\mathbf{X}}||\mathbf{X}||_{\mathrm{F}}^2 = \frac{\partial}{\partial\mathbf{X}}\operatorname{Tr}(\mathbf{X}\mathbf{X}^H) = 2\mathbf{X} \tag{132}`

  See (248). Note that this is also a special case of the result in equation 119.

## Derivatives of Structured Matrices

> Assume that the matrix $`\mathbf{A}` has some structure, i.e. symmetric, toeplitz, etc. In that case the derivatives of the previous section does not apply in general. Instead, consider the following general rule for differentiating a scalar function $`f(\mathbf{A})`

  $$`\frac{df}{dA_{ij}} = \sum_{kl}\frac{\partial f}{\partial A_{kl}}\frac{\partial A_{kl}}{\partial A_{ij}} = \operatorname{Tr}\left[\left[\frac{\partial f}{\partial\mathbf{A}}\right]^T\frac{\partial\mathbf{A}}{\partial A_{ij}}\right] \tag{133}`

  The matrix differentiated with respect to itself is in this document referred to as the _structure matrix_ of $`\mathbf{A}` and is defined simply by

  $$`\frac{\partial\mathbf{A}}{\partial A_{ij}} = \mathbf{S}^{ij} \tag{134}`

  If $`\mathbf{A}` has no special structure we have simply $`\mathbf{S}^{ij} = \mathbf{J}^{ij}`, that is, the structure matrix is simply the single-entry matrix. Many structures have a representation in singleentry matrices, see Sec. 9.7.6 for more examples of structure matrices.

### The Chain Rule

> Sometimes the objective is to find the derivative of a matrix which is a function of another matrix. Let $`\mathbf{U} = f(\mathbf{X})`, the goal is to find the derivative of the function g($`\mathbf{U}`) with respect to $`\mathbf{X}`:

  $$`\frac{\partial g(\mathbf{U})}{\partial\mathbf{X}} = \frac{\partial g(f(\mathbf{X}))}{\partial\mathbf{X}} \tag{135}`

  Then the Chain Rule can then be written the following way:

  $$`\frac{\partial g(\mathbf{U})}{\partial\mathbf{X}} = \frac{\partial g(\mathbf{U})}{\partial x_{ij}} = \sum_{k=1}^M\sum_{l=1}^N\frac{\partial g(\mathbf{U})}{\partial u_{kl}}\frac{\partial u_{kl}}{\partial x_{ij}} \tag{136}`

  Using matrix notation, this can be written as:

  $$`\frac{\partial g(\mathbf{U})}{\partial X_{ij}} = \operatorname{Tr}\Big[(\frac{\partial g(\mathbf{U})}{\partial\mathbf{U}})^T\frac{\partial\mathbf{U}}{\partial X_{ij}}\Big]. \tag{137}`

### Symmetric

> If $`\mathbf{A}` is symmetric, then $`\mathbf{S}^{ij} = \mathbf{J}^{ij} + \mathbf{J}^{ji} - \mathbf{J}^{ij}\mathbf{J}^{ij}` and therefore

  $$`\frac{df}{d\mathbf{A}} = \left[\frac{\partial f}{\partial\mathbf{A}}\right] + \left[\frac{\partial f}{\partial\mathbf{A}}\right]^T - \operatorname{diag}\left[\frac{\partial f}{\partial\mathbf{A}}\right] \tag{138}`

  That is, e.g., (\[5\]):

  $$`\frac{\partial\operatorname{Tr}(\mathbf{A}\mathbf{X})}{\partial\mathbf{X}} = \mathbf{A} + \mathbf{A}^T - (\mathbf{A}\circ\mathbf{I}), \text{ see (142)} \tag{139}`

  $$`\frac{\partial\det(\mathbf{X})}{\partial\mathbf{X}} = \det(\mathbf{X})(2\mathbf{X}^{-1} - (\mathbf{X}^{-1}\circ\mathbf{I})) \tag{140}`

  $$`\frac{\partial\ln\det(\mathbf{X})}{\partial\mathbf{X}} = 2\mathbf{X}^{-1} - (\mathbf{X}^{-1}\circ\mathbf{I}) \tag{141}`

### Diagonal

> If $`\mathbf{X}` is diagonal, then (\[19\]):

  $$`\frac{\partial\operatorname{Tr}(\mathbf{A}\mathbf{X})}{\partial\mathbf{X}} = \mathbf{A}\circ\mathbf{I} \tag{142}`

### Toeplitz

> Like symmetric matrices and diagonal matrices also Toeplitz matrices has a special structure which should be taken into account when the derivative with respect to a matrix with Toeplitz structure.

  $$`\begin{aligned} & \frac{\partial\operatorname{Tr}(\mathbf{A}\mathbf{T})}{\partial\mathbf{T}} \\ = {} & \frac{\partial\operatorname{Tr}(\mathbf{T}\mathbf{A})}{\partial\mathbf{T}} \\ = {} & {\scriptsize \begin{bmatrix} \operatorname{Tr}(\mathbf{A}) & \operatorname{Tr}([\mathbf{A}^T]_{n1}) & \operatorname{Tr}([[\mathbf{A}^T]_{1n}]_{n-1,2}) & \cdots & A_{n1} \\ \operatorname{Tr}([\mathbf{A}^T]_{1n})) & \operatorname{Tr}(\mathbf{A}) & \ddots & \ddots & \vdots \\ \operatorname{Tr}([[\mathbf{A}^T]_{1n}]_{2,n-1}) & \ddots & \ddots & \ddots & \operatorname{Tr}([[\mathbf{A}^T]_{1n}]_{n-1,2}) \\ \vdots & \ddots & \ddots & \ddots & \operatorname{Tr}([\mathbf{A}^T]_{n1}) \\ A_{1n} & \cdots & \operatorname{Tr}([[\mathbf{A}^T]_{1n}]_{2,n-1}) & \operatorname{Tr}([\mathbf{A}^T]_{1n})) & \operatorname{Tr}(\mathbf{A}) \end{bmatrix}} \\ \equiv {} & \boldsymbol{\alpha}(\mathbf{A}) \end{aligned} \tag{143}`

  As it can be seen, the derivative $`\boldsymbol{\alpha}(\mathbf{A})` also has a Toeplitz structure. Each value in the diagonal is the sum of all the diagonal valued in $`\mathbf{A}`, the values in the diagonals next to the main diagonal equal the sum of the diagonal next to the main diagonal in $`\mathbf{A}^T`. This result is only valid for the unconstrained Toeplitz matrix. If the Toeplitz matrix also is symmetric, the same derivative yields

  $$`\frac{\partial\operatorname{Tr}(\mathbf{A}\mathbf{T})}{\partial\mathbf{T}} = \frac{\partial\operatorname{Tr}(\mathbf{T}\mathbf{A})}{\partial\mathbf{T}} = \boldsymbol{\alpha}(\mathbf{A}) + \boldsymbol{\alpha}(\mathbf{A})^T - \boldsymbol{\alpha}(\mathbf{A})\circ\mathbf{I} \tag{144}`
-/

end MatrixCookbook
