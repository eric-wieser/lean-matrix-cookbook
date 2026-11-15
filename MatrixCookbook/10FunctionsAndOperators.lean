module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.RingTheory.PowerSeries.Basic
public import Mathlib.Analysis.Normed.Algebra.MatrixExponential
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.Vec
public import Mathlib.Analysis.CStarAlgebra.Matrix

set_option doc.verso true

/-!
# Functions and Operators

## Functions and Series

### Finite Series
-/

@[expose] public section

variable {ι : Type*} {R : Type*} {l m n p q r : Type*}

variable [Fintype l] [Fintype m] [Fintype n] [Fintype p] [Fintype q] [Fintype r]

variable [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
  [DecidableEq r]

open scoped Nat BigOperators Matrix NNReal ENNReal

open Matrix

namespace MatrixCookbook

variable [Field R]

/--
> $$`(\mathbf{X}^n-\mathbf{I})(\mathbf{X}-\mathbf{I})^{-1} = \mathbf{I}+\mathbf{X}+\mathbf{X}^2+...+\mathbf{X}^{n-1} \tag{487}`

The pdf does not mention {lit}`hx`!
-/
theorem eq_487 (X : Matrix m m R) (n : ℕ) (hx : (X - 1).det ≠ 0) :
    (X ^ n - 1) * (X - 1)⁻¹ = ∑ i ∈ Finset.range n, X ^ i := by
  rw [← geom_sum_mul X n, mul_nonsing_inv_cancel_right _ _ hx.isUnit]

section
open NormedSpace

/-!
### Taylor Expansion of Scalar Function

> Consider some scalar function $`f(\mathbf{x})` which takes the vector $`\mathbf{x}` as an argument. This we can Taylor expand around $`\mathbf{x}_0`

  $$`f(\mathbf{x}) \cong f(\mathbf{x}_0)+\mathbf{g}(\mathbf{x}_0)^T(\mathbf{x}-\mathbf{x}_0)+\frac{1}{2}(\mathbf{x}-\mathbf{x}_0)^T\mathbf{H}(\mathbf{x}_0)(\mathbf{x}-\mathbf{x}_0) \tag{488}`

  where

  $$`\mathbf{g}(\mathbf{x}_0) = \frac{\partial f(\mathbf{x})}{\partial\mathbf{x}}\Big|_{\mathbf{x}_0} \qquad \mathbf{H}(\mathbf{x}_0) = \frac{\partial^2 f(\mathbf{x})}{\partial\mathbf{x}\partial\mathbf{x}^T}\Big|_{\mathbf{x}_0}`

### Matrix Functions by Infinite Series

> As for analytical functions in one dimension, one can define a matrix function for square matrices $`\mathbf{X}` by an infinite series

  $$`\mathbf{f}(\mathbf{X}) = \sum_{n=0}^\infty c_n\mathbf{X}^n \tag{489}`

  assuming the limit exists and is finite. If the coefficients $`c_n` fulfils $`\sum_n c_n x^n < \infty`, then one can prove that the above series exists and is finite, see \[1\]. Thus for any analytical function $`f(x)` there exists a corresponding matrix function $`\mathbf{f}(\mathbf{x})` constructed by the Taylor expansion. Using this one can prove the following results:

  1) A matrix $`\mathbf{A}` is a zero of its own characteristic polynomium \[1\]:

  $$`p(\lambda) = \det(\mathbf{I}\lambda-\mathbf{A}) = \sum_n c_n\lambda^n \qquad\Rightarrow\qquad p(\mathbf{A}) = \mathbf{0} \tag{490}`

  2) If $`\mathbf{A}` is square it holds that \[1\]

  $$`\mathbf{A} = \mathbf{U}\mathbf{B}\mathbf{U}^{-1} \quad\Rightarrow\quad \mathbf{f}(\mathbf{A}) = \mathbf{U}\mathbf{f}(\mathbf{B})\mathbf{U}^{-1} \tag{491}`

  3) A useful fact when using power series is that

  $$`\mathbf{A}^n\rightarrow\mathbf{0}\text{for}n\rightarrow\infty \qquad \text{if} \qquad |\mathbf{A}| < 1 \tag{492}`

### Identity and commutations

> It holds for an analytical matrix function $`\mathbf{f}(\mathbf{X})` that

  $$`\mathbf{f}(\mathbf{A}\mathbf{B})\mathbf{A} = \mathbf{A}\mathbf{f}(\mathbf{B}\mathbf{A}) \tag{493}`

  see B.1.2 for a proof.

### Exponential Matrix Function
-/

/--
> In analogy to the ordinary scalar exponential function, one can define exponential and logarithmic matrix functions:

  $$`e^{\mathbf{A}} \equiv \sum_{n=0}^\infty\frac{1}{n!}\mathbf{A}^n = \mathbf{I}+\mathbf{A}+\frac{1}{2}\mathbf{A}^2+... \tag{494}`
-/
theorem eq_494 (A : Matrix n n ℝ) : exp A = ∑' n : ℕ, (n !⁻¹ : ℝ) • A ^ n := by rw [exp_eq_tsum ℝ]

/--
> $$`e^{-\mathbf{A}} \equiv \sum_{n=0}^\infty\frac{1}{n!}(-1)^n\mathbf{A}^n = \mathbf{I}-\mathbf{A}+\frac{1}{2}\mathbf{A}^2-... \tag{495}`
-/
theorem eq_495 (A : Matrix n n ℝ) : exp (-A) = ∑' n : ℕ, (n !⁻¹ : ℝ) • (-1 : Matrix _ _ ℝ) ^ n * A ^ n := by
  simp_rw [exp_eq_tsum ℝ, neg_pow A, smul_mul_assoc]

/--
> $$`e^{t\mathbf{A}} \equiv \sum_{n=0}^\infty\frac{1}{n!}(t\mathbf{A})^n = \mathbf{I}+t\mathbf{A}+\frac{1}{2}t^2\mathbf{A}^2+... \tag{496}`
-/
theorem eq_496 (t : ℝ) (A : Matrix n n ℝ) : exp (t • A) = ∑' n : ℕ, (n !⁻¹ : ℝ) • t ^ (n : ℕ) • A ^ n := by simp_rw [exp_eq_tsum ℝ, smul_pow]

/-!
> $$`\ln(\mathbf{I}+\mathbf{A}) \equiv \sum_{n=1}^\infty\frac{(-1)^{n-1}}{n}\mathbf{A}^n = \mathbf{A}-\frac{1}{2}\mathbf{A}^2+\frac{1}{3}\mathbf{A}^3-... \tag{497}`
-/

/--
> Some of the properties of the exponential function are \[1\]

  $$`e^{\mathbf{A}}e^{\mathbf{B}} = e^{\mathbf{A}+\mathbf{B}} \qquad \text{if} \qquad \mathbf{A}\mathbf{B} = \mathbf{B}\mathbf{A} \tag{498}`
-/
theorem eq_498 (A B : Matrix n n ℝ) (h : A * B = B * A) : exp A * exp B = exp (A + B) :=
  (Matrix.exp_add_of_commute A B h).symm

/--
> $$`(e^{\mathbf{A}})^{-1} = e^{-\mathbf{A}} \tag{499}`
-/
theorem eq_499 (A : Matrix n n ℝ) : (exp A)⁻¹ = exp (-A) :=
  (Matrix.exp_neg A).symm

end

open scoped Kronecker

/-!
> $$`\frac{d}{dt}e^{t\mathbf{A}} = \mathbf{A}e^{t\mathbf{A}} = e^{t\mathbf{A}}\mathbf{A}, \qquad t\in\mathbb{R} \tag{500}`

  $$`\frac{d}{dt}\operatorname{Tr}(e^{t\mathbf{A}}) = \operatorname{Tr}(\mathbf{A}e^{t\mathbf{A}}) \tag{501}`

  $$`\det(e^{\mathbf{A}}) = e^{\operatorname{Tr}(\mathbf{A})} \tag{502}`

### Trigonometric Functions

> $$`\sin(\mathbf{A}) \equiv \sum_{n=0}^\infty\frac{(-1)^n\mathbf{A}^{2n+1}}{(2n+1)!} = \mathbf{A}-\frac{1}{3!}\mathbf{A}^3+\frac{1}{5!}\mathbf{A}^5-... \tag{503}`

  $$`\cos(\mathbf{A}) \equiv \sum_{n=0}^\infty\frac{(-1)^n\mathbf{A}^{2n}}{(2n)!} = \mathbf{I}-\frac{1}{2!}\mathbf{A}^2+\frac{1}{4!}\mathbf{A}^4-... \tag{504}`

## Kronecker and Vec Operator

### The Kronecker Product
-/

/--
> The Kronecker product of an $`m\times n` matrix $`\mathbf{A}` and an $`r\times q` matrix $`\mathbf{B}`, is an $`mr\times nq` matrix, $`\mathbf{A}\otimes\mathbf{B}` defined as

  $$`\mathbf{A}\otimes\mathbf{B} = \begin{bmatrix} A_{11}\mathbf{B} & A_{12}\mathbf{B} & ... & A_{1n}\mathbf{B} \\ A_{21}\mathbf{B} & A_{22}\mathbf{B} & ... & A_{2n}\mathbf{B} \\ \vdots & & & \vdots \\ A_{m1}\mathbf{B} & A_{m2}\mathbf{B} & ... & A_{mn}\mathbf{B} \end{bmatrix} \tag{505}`
-/
theorem eq_505 (A : Matrix m n R) (B : Matrix r q R) :
    A ⊗ₖ B = Matrix.of fun i j : _ × _ => (A i.1 j.1 • B) i.2 j.2 :=
  rfl

/--
> The Kronecker product has the following properties (see \[19\])

  $$`\mathbf{A}\otimes(\mathbf{B}+\mathbf{C}) = \mathbf{A}\otimes\mathbf{B}+\mathbf{A}\otimes\mathbf{C} \tag{506}`
-/
theorem eq_506 (A : Matrix m n R) (B C : Matrix r q R) : A ⊗ₖ (B + C) = A ⊗ₖ B + A ⊗ₖ C :=
  kronecker_add _ _ _

/--
> $$`\mathbf{A}\otimes\mathbf{B} \neq \mathbf{B}\otimes\mathbf{A} \qquad \text{in general} \tag{507}`
-/
theorem eq_507 [Nontrivial m] [Nonempty n] :
    ¬∀ (A : Matrix m n R) (B : Matrix m n R), A ⊗ₖ B = B ⊗ₖ A := by
  intro h
  obtain ⟨m1, m2, hm⟩ := exists_pair_ne m
  obtain ⟨n1⟩ := id ‹Nonempty n›
  let A := single m1 n1 (1 : R)
  let B := single m2 n1 (1 : R)
  have := Matrix.ext_iff.mpr (h A B) (m1, m2) (n1, n1)
  simp [single_apply_same, single_apply_of_row_ne hm,
    mul_zero, mul_one, one_ne_zero, A, B] at this

/--
> $$`\mathbf{A}\otimes(\mathbf{B}\otimes\mathbf{C}) = (\mathbf{A}\otimes\mathbf{B})\otimes\mathbf{C} \tag{508}`

Note we have to "cast" between the types
-/
theorem eq_508 (A : Matrix m n R) (B : Matrix r q R) (C : Matrix l p R) :
    A ⊗ₖ (B ⊗ₖ C) = reindex (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _) (A ⊗ₖ B ⊗ₖ C) :=
  (kronecker_assoc _ _ _).symm

/--
> $$`(\alpha_A\mathbf{A}\otimes\alpha_B\mathbf{B}) = \alpha_A\alpha_B(\mathbf{A}\otimes\mathbf{B}) \tag{509}`
-/
theorem eq_509 (a b : R) (A : Matrix m n R) (B : Matrix r q R) :
    (a • A) ⊗ₖ (b • B) = (a * b) • A ⊗ₖ B := by rw [smul_kronecker, kronecker_smul, smul_smul]

/--
> $$`(\mathbf{A}\otimes\mathbf{B})^T = \mathbf{A}^T\otimes\mathbf{B}^T \tag{510}`
-/
theorem eq_510 (A : Matrix m n R) (B : Matrix r q R) : (A ⊗ₖ B)ᵀ = Aᵀ ⊗ₖ Bᵀ := by
  rw [kroneckerMap_transpose]

/--
> $$`(\mathbf{A}\otimes\mathbf{B})(\mathbf{C}\otimes\mathbf{D}) = \mathbf{A}\mathbf{C}\otimes\mathbf{B}\mathbf{D} \tag{511}`
-/
theorem eq_511 (A : Matrix l m R) (B : Matrix p q R) (C : Matrix m n R) (D : Matrix q r R) :
    A ⊗ₖ B * C ⊗ₖ D = (A * C) ⊗ₖ (B * D) := by rw [Matrix.mul_kronecker_mul]

/--
> $$`(\mathbf{A}\otimes\mathbf{B})^{-1} = \mathbf{A}^{-1}\otimes\mathbf{B}^{-1} \tag{512}`
-/
theorem eq_512 (A : Matrix m m R) (B : Matrix n n R) : (A ⊗ₖ B)⁻¹ = A⁻¹ ⊗ₖ B⁻¹ :=
  inv_kronecker _ _

/--
> $$`(\mathbf{A}\otimes\mathbf{B})^+ = \mathbf{A}^+\otimes\mathbf{B}^+ \tag{513}`
-/
lemma eq_513 : (sorry : Prop) := sorry

/--
> $$`\operatorname{rank}(\mathbf{A}\otimes\mathbf{B}) = \operatorname{rank}(\mathbf{A})\operatorname{rank}(\mathbf{B}) \tag{514}`
-/
lemma eq_514 (A : Matrix l m R) (B : Matrix p q R) : rank (A ⊗ₖ B) = rank A * rank B := sorry

/--
> $$`\operatorname{Tr}(\mathbf{A}\otimes\mathbf{B}) = \operatorname{Tr}(\mathbf{A})\operatorname{Tr}(\mathbf{B}) = \operatorname{Tr}(\mathbf{\Lambda}_A\otimes\mathbf{\Lambda}_B) \tag{515}`
-/
theorem eq_515 (A : Matrix m m R) (B : Matrix n n R) : trace (A ⊗ₖ B) = trace A * trace B :=
  trace_kronecker _ _

/--
> $$`\det(\mathbf{A}\otimes\mathbf{B}) = \det(\mathbf{A})^{\operatorname{rank}(\mathbf{B})}\det(\mathbf{B})^{\operatorname{rank}(\mathbf{A})} \tag{516}`
-/
theorem eq_516 (A : Matrix m m R) (B : Matrix n n R) :
    det (A ⊗ₖ B) = det A ^ Fintype.card n * det B ^ Fintype.card m :=
  det_kronecker _ _

/--
> $$`\{\operatorname{eig}(\mathbf{A}\otimes\mathbf{B})\} = \{\operatorname{eig}(\mathbf{B}\otimes\mathbf{A})\} \qquad \text{if } \mathbf{A},\mathbf{B} \text{ are square} \tag{517}`
-/
lemma eq_517 : (sorry : Prop) := sorry
/--
> $$`\begin{aligned} \{\operatorname{eig}(\mathbf{A}\otimes\mathbf{B})\} &= \{\operatorname{eig}(\mathbf{A})\operatorname{eig}(\mathbf{B})^T\} \\ &\qquad \text{if } \mathbf{A},\mathbf{B} \text{ are symmetric and square} \end{aligned} \tag{518}`
-/
lemma eq_518 : (sorry : Prop) := sorry
/--
> $$`\operatorname{eig}(\mathbf{A}\otimes\mathbf{B}) = \operatorname{eig}(\mathbf{A})\otimes\operatorname{eig}(\mathbf{B}) \tag{519}`
-/
lemma eq_519 : (sorry : Prop) := sorry

/-!
> Where $`\{\lambda_i\}` denotes the set of values $`\lambda_i`, that is, the values in no particular order or structure, and $`\mathbf{\Lambda}_A` denotes the diagonal matrix with the eigenvalues of $`\mathbf{A}`.

### The Vec Operator

> The vec-operator applied on a matrix $`\mathbf{A}` stacks the columns into a vector, i.e. for a $`2\times 2` matrix

  $$`\mathbf{A} = \begin{bmatrix} A_{11} & A_{12} \\ A_{21} & A_{22} \end{bmatrix} \qquad \operatorname{vec}(\mathbf{A}) = \begin{bmatrix} A_{11} \\ A_{21} \\ A_{12} \\ A_{22} \end{bmatrix}`
-/

/--
> Properties of the vec-operator include (see \[19\])

  $$`\operatorname{vec}(\mathbf{A}\mathbf{X}\mathbf{B}) = (\mathbf{B}^T\otimes\mathbf{A})\operatorname{vec}(\mathbf{X}) \tag{520}`
-/
theorem eq_520 (A : Matrix l m R) (X : Matrix m n R) (B : Matrix n p R) :
    vec (A * X * B) = Bᵀ ⊗ₖ A *ᵥ vec X := by
  rw [kronecker_mulVec_vec, transpose_transpose]

/--
> $$`\operatorname{Tr}(\mathbf{A}^T\mathbf{B}) = \operatorname{vec}(\mathbf{A})^T\operatorname{vec}(\mathbf{B}) \tag{521}`
-/
theorem eq_521 (A B : Matrix m n R) : (Aᵀ * B).trace = (vec A ⬝ᵥ vec B) :=
  (vec_dotProduct_vec _ _).symm

/--
> $$`\operatorname{vec}(\mathbf{A}+\mathbf{B}) = \operatorname{vec}(\mathbf{A})+\operatorname{vec}(\mathbf{B}) \tag{522}`
-/
theorem eq_522 (A B : Matrix m n R) : vec (A + B) = vec A + vec B := vec_add _ _

/--
> $$`\operatorname{vec}(\alpha\mathbf{A}) = \alpha\cdot\operatorname{vec}(\mathbf{A}) \tag{523}`
-/
theorem eq_523 (r : R) (A : Matrix m n R) : vec (r • A) = r • vec A := vec_smul _ _

/--
> $$`\mathbf{a}^T\mathbf{X}\mathbf{B}\mathbf{X}^T\mathbf{c} = \operatorname{vec}(\mathbf{X})^T(\mathbf{B}\otimes\mathbf{c}\mathbf{a}^T)\operatorname{vec}(\mathbf{X}) \tag{524}`
-/
-- note: `Bᵀ` is `B` in the PDF
theorem eq_524 (a : m → R) (X : Matrix m n R) (B : Matrix n n R) (c : m → R) :
    a ᵥ* (X * B * Xᵀ) ⬝ᵥ c = vec X ᵥ* (Bᵀ ⊗ₖ vecMulVec c a) ⬝ᵥ vec X := by
  -- not the proof from the book
  simp only [vec, dotProduct, vecMul, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum, Matrix.kroneckerMap_apply,
    transpose_apply]
  simp_rw [← Finset.univ_product_univ, Finset.sum_product, @Finset.sum_comm n _ m, vecMulVec,
    of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun kk _ => ?_
  refine Finset.sum_congr rfl fun ll _ => ?_
  ring

/-!
> See B.1.1 for a proof for Eq. 524.

## Vector Norms

### Examples
-/

/--
> $$`||\mathbf{x}||_1 = \sum_i|x_i| \tag{525}`
-/
theorem eq_525 (x : n → ℂ) : ‖WithLp.toLp 1 x‖ = ∑ i, ‖x i‖ := by
  simpa using PiLp.norm_eq_of_nat 1 Nat.cast_one.symm (WithLp.toLp 1 x)

/--
> $$`||\mathbf{x}||_2^2 = \mathbf{x}^H\mathbf{x} \tag{526}`
-/
theorem eq_526 (x : n → ℂ) : ↑(‖WithLp.toLp 2 x‖ ^ 2 : ℝ) = star x ⬝ᵥ x := by
  rw [dotProduct_comm, ← EuclideanSpace.inner_toLp_toLp, inner_self_eq_norm_sq_to_K,
    Complex.ofReal_pow]
  rfl

/--
> $$`||\mathbf{x}||_p = \left[\sum_i|x_i|^p\right]^{1/p} \tag{527}`
-/
theorem eq_527 (x : n → ℂ) (p : ℝ≥0∞) (h : 0 < p.toReal) :
    ‖WithLp.toLp p x‖ = (∑ i, ‖x i‖ ^ p.toReal) ^ (1 / p.toReal) := by
  simp_rw [PiLp.norm_eq_sum h]

/--
> $$`||\mathbf{x}||_\infty = \max_i|x_i| \tag{528}`
-/
theorem eq_528 (x : n → ℂ) : ‖WithLp.toLp ∞ x‖ = ⨆ i, ‖x i‖ := by
  simp_rw [PiLp.norm_eq_ciSup]

/-!
> Further reading in e.g. \[12, p. 52\]

## Matrix Norms

### Definitions
-/

/--
> A matrix norm is a mapping which fulfils

  $$`||\mathbf{A}|| \geq 0 \tag{529}`
-/
theorem eq_529 (A : Matrix n n ℝ) : open scoped Matrix.Norms.Elementwise in 0 ≤ ‖A‖ :=
  open scoped Matrix.Norms.Elementwise in norm_nonneg _

/--
> $$`||\mathbf{A}|| = 0 \Leftrightarrow \mathbf{A} = \mathbf{0} \tag{530}`
-/
theorem eq_530 (A : Matrix n n ℝ) : open scoped Matrix.Norms.Elementwise in ‖A‖ = 0 ↔ A = 0 :=
  open scoped Matrix.Norms.Elementwise in norm_eq_zero

/--
> $$`||c\mathbf{A}|| = |c|||\mathbf{A}||, \qquad c\in\mathbb{R} \tag{531}`
-/
theorem eq_531 (r : ℝ) (A : Matrix n n ℝ) :
    open scoped Matrix.Norms.Elementwise in ‖r • A‖ = |r| * ‖A‖ := by
  open scoped Matrix.Norms.Elementwise in rw [norm_smul r A, Real.norm_eq_abs]

/--
> $$`||\mathbf{A}+\mathbf{B}|| \leq ||\mathbf{A}||+||\mathbf{B}|| \tag{532}`
-/
theorem eq_532 (A B : Matrix n n ℝ) : open scoped Matrix.Norms.Elementwise in ‖A + B‖ ≤ ‖A‖ + ‖B‖ :=
  open scoped Matrix.Norms.Elementwise in norm_add_le _ _

-- we just use one of the norms as an example; there is no generalization available
section

open scoped Matrix.Norms.Operator

/-!
### Induced Norm or Operator Norm
-/

/--
> An induced norm is a matrix norm induced by a vector norm by the following

  $$`||\mathbf{A}|| = \sup\{||\mathbf{A}\mathbf{x}|| \quad | \quad ||\mathbf{x}|| = 1\} \tag{533}`
-/
lemma eq_533 (A : Matrix m n ℝ) : ‖A‖ = sSup { ‖A.mulVec x‖ | (x) (_ : ‖x‖ = 1)} := by
  suffices ‖A‖ = sSup ((‖A.mulVec ·‖) '' Metric.sphere 0 1) by
    simpa [Set.image, mem_sphere_zero_iff_norm] using this
  simp_rw [linfty_opNorm_eq_opNorm, ← ContinuousLinearMap.sSup_sphere_eq_norm]
  simp

/--
> where $`||\cdot||` on the left side is the induced matrix norm, while $`||\cdot||` on the right side denotes the vector norm. For induced norms it holds that

  $$`||\mathbf{I}|| = 1 \tag{534}`
-/
theorem eq_534 [Nonempty n] : ‖(1 : Matrix n n ℝ)‖ = 1 :=
  norm_one

/--
> $$`||\mathbf{A}\mathbf{x}|| \leq ||\mathbf{A}||\cdot||\mathbf{x}||, \qquad \text{for all } \mathbf{A},\mathbf{x} \tag{535}`
-/
theorem eq_535 (A : Matrix m n ℝ) (x : n → ℝ) : ‖A.mulVec x‖ ≤ ‖A‖ * ‖x‖ :=
  linfty_opNorm_mulVec _ _

/--
> $$`||\mathbf{A}\mathbf{B}|| \leq ||\mathbf{A}||\cdot||\mathbf{B}||, \qquad \text{for all } \mathbf{A},\mathbf{B} \tag{536}`
-/
theorem eq_536 (A : Matrix m n ℝ) (B : Matrix n p ℝ) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ :=
  linfty_opNorm_mul _ _

end

/-!
### Examples
-/

/--
> $$`||\mathbf{A}||_1 = \max_j\sum_i|A_{ij}| \tag{537}`
-/
lemma eq_537 (A : Matrix m n ℝ) : sorry = ⨆ j, ∑ i, ‖A i j‖ := sorry

/--
> $$`||\mathbf{A}||_2 = \sqrt{\max\operatorname{eig}(\mathbf{A}^H\mathbf{A})} \tag{538}`
-/
lemma eq_538 (A : Matrix m n ℝ) :
    (open scoped Matrix.Norms.L2Operator in ‖A‖) =
      NNReal.sqrt (Finset.univ.sup fun i => ⟨_, A.eigenvalues_conjTranspose_mul_self_nonneg i⟩) := sorry

/--
> $$`||\mathbf{A}||_p = (\max_{||\mathbf{x}||_p=1}||\mathbf{A}\mathbf{x}||_p)^{1/p} \tag{539}`
-/
lemma eq_539 : (sorry : Prop) := sorry

/--
> $$`||\mathbf{A}||_\infty = \max_i\sum_j|A_{ij}| \tag{540}`
-/
theorem eq_540 (A : Matrix m n ℝ) :
    (open scoped Matrix.Norms.Operator in ‖A‖) =
      ↑(Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) := by
  rw [linfty_opNorm_def]

/--
> $$`||\mathbf{A}||_{\mathrm{F}} = \sqrt{\sum_{ij}|A_{ij}|^2} = \sqrt{\operatorname{Tr}(\mathbf{A}\mathbf{A}^H)} \qquad (\text{Frobenius}) \tag{541}`
-/
theorem eq_541 (A : Matrix m n ℝ) :
    (open scoped Matrix.Norms.Frobenius in ‖A‖) =
      Real.sqrt (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) := by
  rw [frobenius_norm_def, Real.sqrt_eq_rpow]

/--
> $$`||\mathbf{A}||_{\max} = \max_{ij}|A_{ij}| \tag{542}`
-/
theorem eq_542 (A : Matrix m n ℝ) :
    (open scoped Matrix.Norms.Elementwise in ‖A‖) =
      ↑(Finset.univ.sup fun ij : _ × _ => ‖A ij.1 ij.2‖₊) := by
  open scoped Matrix.Norms.Elementwise in
  rw [← coe_nnnorm, Matrix.nnnorm_def, Pi.nnnorm_def, ← Finset.univ_product_univ,
    Finset.sup_product_left]
  simp_rw [Pi.nnnorm_def]

/--
> $$`||\mathbf{A}||_{\mathrm{KF}} = ||\operatorname{sing}(\mathbf{A})||_1 \qquad (\text{Ky Fan}) \tag{543}`
-/
lemma eq_543 : (sorry : Prop) := sorry

/-!
> where $`\operatorname{sing}(\mathbf{A})` is the vector of singular values of the matrix $`\mathbf{A}`.

### Inequalities

> E. H. Rasmussen has in yet unpublished material derived and collected the following inequalities. They are collected in a table as below, assuming $`\mathbf{A}` is an $`m\times n`, and $`d = \operatorname{rank}(\mathbf{A})`

  $$`\begin{array}{c|cccccc} & ||\mathbf{A}||_{\max} & ||\mathbf{A}||_1 & ||\mathbf{A}||_\infty & ||\mathbf{A}||_2 & ||\mathbf{A}||_{\mathrm{F}} & ||\mathbf{A}||_{\mathrm{KF}} \\ \hline ||\mathbf{A}||_{\max} & & 1 & 1 & 1 & 1 & 1 \\ ||\mathbf{A}||_1 & m & & m & \sqrt{m} & \sqrt{m} & \sqrt{m} \\ ||\mathbf{A}||_\infty & n & n & & \sqrt{n} & \sqrt{n} & \sqrt{n} \\ ||\mathbf{A}||_2 & \sqrt{mn} & \sqrt{n} & \sqrt{m} & & 1 & 1 \\ ||\mathbf{A}||_{\mathrm{F}} & \sqrt{mn} & \sqrt{n} & \sqrt{m} & \sqrt{d} & & 1 \\ ||\mathbf{A}||_{\mathrm{KF}} & \sqrt{mnd} & \sqrt{nd} & \sqrt{md} & d & \sqrt{d} & \end{array}`
-/

/--
> which are to be read as, e.g.

  $$`||\mathbf{A}||_2 \leq \sqrt{m}\cdot||\mathbf{A}||_\infty \tag{544}`
-/
-- TODO: are the bounds tight?
lemma eq_544 (A : Matrix m n ℝ) :
    letI m' := Fintype.card m
    letI n' := Fintype.card n
    letI d := A.rank
    let norms : Fin 6 → (Matrix m n ℝ → ℝ) := ![
      open scoped Norms.Elementwise in (‖·‖),
      sorry, -- L1 norm
      open scoped Norms.Operator in (‖·‖),
      open scoped Norms.L2Operator in (‖·‖),
      open scoped Norms.Frobenius in (‖·‖),
      sorry -- Ky Fan norm
    ]
    let coeffs : Matrix _ _ ℝ := !![
      1,                   1,              1,              1,        1,        1;
      m',                  1,              m',             .sqrt m', .sqrt m', .sqrt m';
      n',                  n',             1,              .sqrt n', .sqrt n', .sqrt n';
      .sqrt (m' * n'),     .sqrt n',       .sqrt m',       1,        1,        1;
      .sqrt (m' * n'),     .sqrt n',       .sqrt m',       .sqrt d,  1,        1;
      .sqrt (m' * n' * d), .sqrt (n' * d), .sqrt (m' * d), d,        .sqrt d,  1]
    ∀ i j, norms i A ≤ coeffs i j * norms j A := by
  -- unpack the matrix into the elements
  simp only [Fin.forall_fin_succ, IsEmpty.forall_iff, and_true, Matrix.of_apply, Fin.reduceSucc,
    cons_val, one_mul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  -- the diagonal elements are easy, but 30 missing lemmas remain
  · refine ⟨le_rfl, sorry, sorry, sorry, sorry, sorry⟩
  · refine ⟨sorry, le_rfl, sorry, sorry, sorry, sorry⟩
  · refine ⟨sorry, sorry, le_rfl, sorry, sorry, sorry⟩
  · refine ⟨sorry, sorry, sorry, le_rfl, sorry, sorry⟩
  · refine ⟨sorry, sorry, sorry, sorry, le_rfl, sorry⟩
  · refine ⟨sorry, sorry, sorry, sorry, sorry, le_rfl⟩

/-!
### Condition Number
-/

section

open scoped Matrix.Norms.L2Operator

/--
> The 2-norm of $`\mathbf{A}` equals $`\sqrt{(\max(\operatorname{eig}(\mathbf{A}^T\mathbf{A})))}` \[12, p.57\]. For a symmetric, positive definite matrix, this reduces to $`\max(\operatorname{eig}(\mathbf{A}))` The condition number based on the 2-norm thus reduces to

  $$`\|\mathbf{A}\|_2\|\mathbf{A}^{-1}\|_2 = \max(\operatorname{eig}(\mathbf{A}))\max(\operatorname{eig}(\mathbf{A}^{-1})) = \frac{\max(\operatorname{eig}(\mathbf{A}))}{\min(\operatorname{eig}(\mathbf{A}))}. \tag{545}`
-/
lemma eq_545 (A : Matrix n n ℝ) : ‖A‖ * ‖A⁻¹‖ = sorry / sorry := sorry

end

/-!
## Rank

### Sylvester's Inequality
-/

/--
> If $`\mathbf{A}` is $`m\times n` and $`\mathbf{B}` is $`n\times r`, then

  $$`\operatorname{rank}(\mathbf{A})+\operatorname{rank}(\mathbf{B})-n \leq \operatorname{rank}(\mathbf{A}\mathbf{B}) \leq \min\{\operatorname{rank}(\mathbf{A}),\operatorname{rank}(\mathbf{B})\} \tag{546}`
-/
theorem eq_546 (A : Matrix m n ℝ) (B : Matrix n r ℝ) :
    rank A + rank B - Fintype.card n ≤ rank (A * B) ∧ rank (A * B) ≤ min (rank A) (rank B) :=
  ⟨tsub_le_iff_right.mpr (rank_mul_ge A B), rank_mul_le _ _⟩

/-!
## Integral Involving Dirac Delta Functions
-/

/--
> Assuming $`\mathbf{A}` to be square, then

  $$`\int p(\mathbf{s})\delta(\mathbf{x}-\mathbf{A}\mathbf{s})d\mathbf{s} = \frac{1}{\det(\mathbf{A})}p(\mathbf{A}^{-1}\mathbf{x}) \tag{547}`
-/
lemma eq_547 : (sorry : Prop) := sorry
/--
> Assuming $`\mathbf{A}` to be "underdetermined", i.e. "tall", then

  $$`\int p(\mathbf{s})\delta(\mathbf{x}-\mathbf{A}\mathbf{s})d\mathbf{s} = \left\{\begin{array}{ll} \frac{1}{\sqrt{\det(\mathbf{A}^T\mathbf{A})}}p(\mathbf{A}^+\mathbf{x}) & \text{if } \mathbf{x} = \mathbf{A}\mathbf{A}^+\mathbf{x} \\ 0 & \text{elsewhere} \end{array}\right\} \tag{548}`
-/
lemma eq_548 : (sorry : Prop) := sorry

/-!
> See \[9\].

## Miscellaneous
-/

/--
> For any $`\mathbf{A}` it holds that

  $$`\operatorname{rank}(\mathbf{A}) = \operatorname{rank}(\mathbf{A}^T) = \operatorname{rank}(\mathbf{A}\mathbf{A}^T) = \operatorname{rank}(\mathbf{A}^T\mathbf{A}) \tag{549}`
-/
theorem eq_549 (A : Matrix m n ℝ) :
    A.rank = Aᵀ.rank ∧ A.rank = (A * Aᵀ).rank ∧ A.rank = (Aᵀ * A).rank :=
  ⟨A.rank_transpose.symm, A.rank_self_mul_transpose.symm, A.rank_transpose_mul_self.symm⟩

section

open scoped MatrixOrder Matrix.Norms.L2Operator

/--
> It holds that

  $$`\mathbf{A}\text{ is positive definite} \quad\Leftrightarrow\quad \exists\mathbf{B}\text{ invertible, such that }\mathbf{A} = \mathbf{B}\mathbf{B}^T \tag{550}`
-/
theorem eq_550 (A : Matrix m m ℝ) :
    A.PosDef ↔ ∃ B : Matrix m m ℝ, IsUnit B ∧ A = B * Bᵀ := by
  rw [← isStrictlyPositive_iff_posDef, CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self,
    (Function.RightInverse.surjective transpose_transpose).exists]
  simp [isUnit_transpose, star_eq_conjTranspose]

end

end MatrixCookbook
