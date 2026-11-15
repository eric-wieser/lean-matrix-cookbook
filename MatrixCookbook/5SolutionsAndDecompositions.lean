module

public import Mathlib.Analysis.Matrix.LDL
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.LinearAlgebra.Matrix.Vec
public import MatrixCookbook.ForMathlib.LinearAlgebra.Matrix.Symmetric

set_option doc.verso true

/-!
# Solutions and Decompositions

## Solutions to linear equations

### Simple Linear Regression

> Assume we have data $`(x_n, y_n)` for $`n = 1, ..., N` and are seeking the parameters $`a, b\in\mathbb{R}` such that $`y_i \cong ax_i + b`. With a least squares error function, the optimal values for $`a, b` can be expressed using the notation

  $$`\mathbf{x} = (x_1, ..., x_N)^T \qquad \mathbf{y} = (y_1, ..., y_N)^T \qquad \mathbf{1} = (1, ..., 1)^T \in \mathbb{R}^{N\times 1}`

  and

  $$`\begin{array}{lll} R_{xx} = \mathbf{x}^T\mathbf{x} & R_{x1} = \mathbf{x}^T\mathbf{1} & R_{11} = \mathbf{1}^T\mathbf{1} \\ R_{yx} = \mathbf{y}^T\mathbf{x} & R_{y1} = \mathbf{y}^T\mathbf{1} & \end{array}`
-/

public section

variable {m n p R : Type*}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

open scoped Matrix

namespace MatrixCookbook

/--
> as

  $$`\begin{bmatrix} a \\ b \end{bmatrix} = \begin{bmatrix} R_{xx} & R_{x1} \\ R_{x1} & R_{11} \end{bmatrix}^{-1}\begin{bmatrix} R_{x,y} \\ R_{y1} \end{bmatrix} \tag{260}`
-/
theorem eq_260 : (sorry : Prop) :=
  sorry

/-!
### Existence in Linear Systems
-/

/--
> Assume $`\mathbf{A}` is $`n\times m` and consider the linear system

  $$`\mathbf{A}\mathbf{x} = \mathbf{b} \tag{261}`
-/
theorem eq_261 : (sorry : Prop) :=
  sorry

/-!
> Construct the augmented matrix $`\mathbf{B} = [\mathbf{A}\ \mathbf{b}]` then

  $$`\begin{array}{ll} \textit{Condition} & \textit{Solution} \\ \operatorname{rank}(\mathbf{A}) = \operatorname{rank}(\mathbf{B}) = m & \text{Unique solution } \mathbf{x} \\ \operatorname{rank}(\mathbf{A}) = \operatorname{rank}(\mathbf{B}) < m & \text{Many solutions } \mathbf{x} \\ \operatorname{rank}(\mathbf{A}) < \operatorname{rank}(\mathbf{B}) & \text{No solutions } \mathbf{x} \end{array}`

### Standard Square
-/

/--
> Assume $`\mathbf{A}` is square and invertible, then

  $$`\mathbf{A}\mathbf{x} = \mathbf{b} \qquad\Rightarrow\qquad \mathbf{x} = \mathbf{A}^{-1}\mathbf{b} \tag{262}`
-/
theorem eq_262 [Field R] (A : Matrix n n R) (x b : n → R) (h : IsUnit A) :
    A *ᵥ x = b ↔ x = A⁻¹ *ᵥ b := by
  conv_rhs => rw [← Matrix.mulVec_injective_of_isUnit h|>.eq_iff]
  let := h.invertible
  rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

/-!
### Degenerated Square

> Assume $`\mathbf{A}` is $`n\times n` but of rank $`r < n`. In that case, the system $`\mathbf{A}\mathbf{x} = \mathbf{b}` is solved by

  $$`\mathbf{x} = \mathbf{A}^+\mathbf{b}`

  where $`\mathbf{A}^+` is the pseudo-inverse of the rank-deficient matrix, constructed as described in section 3.6.3.

### Cramer's rule
-/

/--
> The equation

  $$`\mathbf{A}\mathbf{x} = \mathbf{b}, \tag{263}`

This isn't a theorem at all.
-/
theorem eq_263 : True :=
  trivial

/--
> where $`\mathbf{A}` is square has exactly one solution $`\mathbf{x}` if the $`i`th element in $`x` can be found as

  $$`x_i = \frac{\det\mathbf{B}}{\det\mathbf{A}}, \tag{264}`
-/
theorem eq_264 [Field R] (A : Matrix n n R) (x b : n → R) (h : A.det ≠ 0) :
    A *ᵥ x = b ↔ ∀ i, x i = A.det⁻¹ • A.cramerMap b i :=
  ((Matrix.mulVec_injective_of_det_ne_zero h).eq_iff' (b := A.det⁻¹ • A.cramer b) <| by
    rw [Matrix.mulVec_smul, Matrix.mulVec_cramer, inv_smul_smul₀ h]).trans funext_iff

/-!
> where $`\mathbf{B}` equals $`\mathbf{A}`, but the $`i`th column in $`\mathbf{A}` has been substituted by $`\mathbf{b}`.

### Over-determined Rectangular
-/

/--
> Assume $`\mathbf{A}` to be $`n\times m`, $`n > m` (tall) and $`\operatorname{rank}(\mathbf{A}) = m`, then

  $$`\mathbf{A}\mathbf{x} = \mathbf{b} \qquad\Rightarrow\qquad \mathbf{x} = (\mathbf{A}^T\mathbf{A})^{-1}\mathbf{A}^T\mathbf{b} = \mathbf{A}^+\mathbf{b} \tag{265}`
-/
theorem eq_265 : (sorry : Prop) :=
  sorry

/--
> that is _if_ there exists a solution $`\mathbf{x}` at all! If there is no solution the following can be useful:

  $$`\mathbf{A}\mathbf{x} = \mathbf{b} \qquad\Rightarrow\qquad \mathbf{x}_{min} = \mathbf{A}^+\mathbf{b} \tag{266}`
-/
theorem eq_266 : (sorry : Prop) :=
  sorry

/-!
> Now $`\mathbf{x}_{min}` is the vector $`\mathbf{x}` which minimizes $`||\mathbf{A}\mathbf{x}-\mathbf{b}||^2`, i.e. the vector which is "least wrong". The matrix $`\mathbf{A}^+` is the pseudo-inverse of $`\mathbf{A}`. See \[3\].

### Under-determined Rectangular
-/

/--
> Assume $`\mathbf{A}` is $`n\times m` and $`n < m` ("broad") and $`\operatorname{rank}(\mathbf{A}) = n`.

  $$`\mathbf{A}\mathbf{x} = \mathbf{b} \qquad\Rightarrow\qquad \mathbf{x}_{min} = \mathbf{A}^T(\mathbf{A}\mathbf{A}^T)^{-1}\mathbf{b} \tag{267}`
-/
theorem eq_267 : (sorry : Prop) :=
  sorry

/--
> The equation have many solutions $`\mathbf{x}`. But $`\mathbf{x}_{min}` is the solution which minimizes $`||\mathbf{A}\mathbf{x}-\mathbf{b}||^2` and also the solution with the smallest norm $`||\mathbf{x}||^2`. The same holds for a matrix version: Assume $`\mathbf{A}` is $`n\times m`, $`\mathbf{X}` is $`m\times n` and $`\mathbf{B}` is $`n\times n`, then

  $$`\mathbf{A}\mathbf{X} = \mathbf{B} \qquad\Rightarrow\qquad \mathbf{X}_{min} = \mathbf{A}^+\mathbf{B} \tag{268}`
-/
theorem eq_268 : (sorry : Prop) :=
  sorry

/-!
> The equation have many solutions $`\mathbf{X}`. But $`\mathbf{X}_{min}` is the solution which minimizes $`||\mathbf{A}\mathbf{X}-\mathbf{B}||^2` and also the solution with the smallest norm $`||\mathbf{X}||^2`. See \[3\].
-/

/--
> Similar but different: Assume $`\mathbf{A}` is square $`n\times n` and the matrices $`\mathbf{B}_0, \mathbf{B}_1` are $`n\times N`, where $`N > n`, then if $`\mathbf{B}_0` has maximal rank

  $$`\mathbf{A}\mathbf{B}_0 = \mathbf{B}_1 \qquad\Rightarrow\qquad \mathbf{A}_{min} = \mathbf{B}_1\mathbf{B}_0^T(\mathbf{B}_0\mathbf{B}_0^T)^{-1} \tag{269}`
-/
theorem eq_269 : (sorry : Prop) :=
  sorry

/-!
> where $`\mathbf{A}_{min}` denotes the matrix which is optimal in a least square sense. An interpretation is that $`\mathbf{A}` is the linear approximation which maps the columns vectors of $`\mathbf{B}_0` into the columns vectors of $`\mathbf{B}_1`.

### Linear form and zeros
-/

/--
> $$`\mathbf{A}\mathbf{x} = \mathbf{0}, \quad \forall\mathbf{x} \qquad\Rightarrow\qquad \mathbf{A} = \mathbf{0} \tag{270}`
-/
theorem eq_270 (A : Matrix m m ℝ) : (∀ x, A.mulVec x = 0) → A = 0 := by
  intro h
  ext i j
  simpa using congr_fun (h (Pi.single j 1)) i

/-!
### Square form and zeros
-/

/--
> If $`\mathbf{A}` is symmetric, then

  $$`\mathbf{x}^T\mathbf{A}\mathbf{x} = \mathbf{0}, \quad \forall\mathbf{x} \qquad\Rightarrow\qquad \mathbf{A} = \mathbf{0} \tag{271}`
-/
theorem eq_271 (A : Matrix m m ℝ) (hA : A.IsSymm) : (∀ x, x ⬝ᵥ A.mulVec x = 0) → A = 0 :=
  (hA.dotProduct_mulVec_self_eq_zero (.of_ne_zero two_ne_zero)).mp

/-!
### The Lyapunov Equation
-/

/--
> $$`\mathbf{A}\mathbf{X} + \mathbf{X}\mathbf{B} = \mathbf{C} \tag{272}`

This is actually an assumption for the next equation.
-/
theorem eq_272 : True := trivial

section

open scoped Kronecker

/--
> $$`\operatorname{vec}(\mathbf{X}) = (\mathbf{I}\otimes\mathbf{A} + \mathbf{B}^T\otimes\mathbf{I})^{-1}\operatorname{vec}(\mathbf{C}) \tag{273}`
-/
theorem eq_273 (A : Matrix n n ℝ) (B : Matrix n n ℝ) (X : Matrix n n ℝ) (C : Matrix n n ℝ)
    (h : IsUnit (1 ⊗ₖ A + Bᵀ ⊗ₖ 1)) :
    A * X + X * B = C ↔ X.vec = (1 ⊗ₖ A + Bᵀ ⊗ₖ 1)⁻¹ *ᵥ C.vec := by
  let := h.invertible
  rw [← Matrix.mulVec_injective_of_isUnit h |>.eq_iff, Matrix.mulVec_mulVec,
    Matrix.mul_inv_of_invertible, Matrix.one_mulVec, Matrix.add_mulVec, Matrix.kronecker_mulVec_vec,
    Matrix.kronecker_mulVec_vec, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one,
    ← Matrix.vec_add, Matrix.transpose_transpose, Matrix.vec_inj]

end

/-!
> Sec 10.2.1 and 10.2.2 for details on the Kronecker product and the vec operator.

### Encapsulating Sum
-/

/--
> $$`\textstyle\sum_n\mathbf{A}_n\mathbf{X}\mathbf{B}_n = \mathbf{C} \tag{274}`

This is actually an assumption for the next equation.
-/
theorem eq_274 : True := trivial

section

open scoped Kronecker

/--
> $$`\operatorname{vec}(\mathbf{X}) = \big(\textstyle\sum_n\mathbf{B}_n^T\otimes\mathbf{A}_n\big)^{-1}\operatorname{vec}(\mathbf{C}) \tag{275}`
-/
theorem eq_275 [Fintype ι] (A : ι → Matrix n n ℝ) (B : ι → Matrix n n ℝ) (X : Matrix n n ℝ) (C : Matrix n n ℝ)
    (h : IsUnit (∑ i, (B i)ᵀ ⊗ₖ A i)) :
    ∑ i, A i * X * B i = C ↔ X.vec = (∑ i, (B i)ᵀ ⊗ₖ A i)⁻¹ *ᵥ C.vec := by
  let := h.invertible
  rw [← Matrix.mulVec_injective_of_isUnit h |>.eq_iff, Matrix.mulVec_mulVec,
    Matrix.mul_inv_of_invertible, Matrix.one_mulVec, ← funext <| Matrix.mulVec.addMonoidHomLeft_apply _ _,
    map_sum]
  simp_rw [funext <| Matrix.mulVec.addMonoidHomLeft_apply _ _, Matrix.kronecker_mulVec_vec,
    Matrix.transpose_transpose, ← Matrix.vec_sum, Matrix.vec_inj]

end

/-!
> See Sec 10.2.1 and 10.2.2 for details on the Kronecker product and the vec operator.

## Eigenvalues and Eigenvectors

### Definition
-/

/--
> The eigenvectors $`\mathbf{v}_i` and eigenvalues $`\lambda_i` are the ones satisfying

  $$`\mathbf{A}\mathbf{v}_i = \lambda_i\mathbf{v}_i \tag{276}`
-/
theorem eq_276 : (sorry : Prop) :=
  sorry

/-!
### Decompositions
-/

/--
> For matrices $`\mathbf{A}` with as many distinct eigenvalues as dimensions, the following holds, where the columns of $`\mathbf{V}` are the eigenvectors and $`(\mathbf{D})_{ij} = \delta_{ij}\lambda_i`,

  $$`\mathbf{A}\mathbf{V} = \mathbf{V}\mathbf{D} \tag{277}`
-/
theorem eq_277 : (sorry : Prop) :=
  sorry

/--
> For defective matrices $`\mathbf{A}`, which is matrices which has fewer distinct eigenvalues than dimensions, the following decomposition called _Jordan canonical form_, holds

  $$`\mathbf{A}\mathbf{V} = \mathbf{V}\mathbf{J} \tag{278}`
-/
theorem eq_278 : (sorry : Prop) :=
  sorry

/-!
> where $`\mathbf{J}` is a block diagonal matrix with the blocks $`\mathbf{J}_i = \lambda_i\mathbf{I} + \mathbf{N}`. The matrices $`\mathbf{J}_i` have dimensionality as the number of identical eigenvalues equal to $`\lambda_i`, and $`\mathbf{N}` is square matrix of same size with 1 on the super diagonal and zero elsewhere.
-/

/--
> It also holds that for all matrices $`\mathbf{A}` there exists matrices $`\mathbf{V}` and $`\mathbf{R}` such that

  $$`\mathbf{A}\mathbf{V} = \mathbf{V}\mathbf{R} \tag{279}`
-/
theorem eq_279 : (sorry : Prop) :=
  sorry

/-!
> where $`\mathbf{R}` is upper triangular with the eigenvalues $`\lambda_i` on its diagonal.

### General Properties
-/

/--
> Assume that $`\mathbf{A}\in\mathbb{R}^{n\times m}` and $`\mathbf{B}\in\mathbb{R}^{m\times n}`,

  $$`\operatorname{eig}(\mathbf{A}\mathbf{B}) = \operatorname{eig}(\mathbf{B}\mathbf{A}) \tag{280}`
-/
theorem eq_280 : (sorry : Prop) :=
  sorry

/--
> $$`\operatorname{rank}(\mathbf{A}) = r \quad\Rightarrow\quad \text{At most } r \text{ non-zero } \lambda_i \tag{281}`
-/
theorem eq_281 : (sorry : Prop) :=
  sorry

/-!
### Symmetric
-/

/--
> Assume $`\mathbf{A}` is symmetric, then

  $$`\mathbf{V}\mathbf{V}^T = \mathbf{I} \qquad (\text{i.e. } \mathbf{V} \text{ is orthogonal}) \tag{282}`
-/
theorem eq_282 (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix n n ℝ) * hA.eigenvectorUnitaryᵀ = 1 := by
  simpa only [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial]
    using hA.eigenvectorUnitary.prop

/--
> $$`\lambda_i \in \mathbb{R} \qquad (\text{i.e. } \lambda_i \text{ is real}) \tag{283}`
-/
theorem eq_283 (A : Matrix n n ℝ) (hA : A.IsHermitian) (i : n) :
    (fun {α} (_ : α) => α) (hA.eigenvalues i) = ℝ :=
  rfl

/--
> $$`\operatorname{Tr}(\mathbf{A}^p) = \textstyle\sum_i\lambda_i^p \tag{284}`
-/
theorem eq_284 (A : Matrix n n ℝ) (hA : A.IsHermitian) (p : ℕ):
    Matrix.trace (A ^ p) = ∑ i, hA.eigenvalues i ^ p := by
  rw [← cfc_pow_id (R := ℝ) A p hA.isSelfAdjoint, Matrix.trace_eq_neg_charpoly_nextCoeff,
    hA.charpoly_cfc_eq, Polynomial.prod_X_sub_C_nextCoeff, neg_neg]
  simp

/--
> $$`\operatorname{eig}(\mathbf{I}+c\mathbf{A}) = 1 + c\lambda_i \tag{285}`
-/
theorem eq_285 (A : Matrix n n ℝ) (c : ℝ) (hA : A.IsHermitian) :
    (Matrix.isHermitian_one.add (hA.map (c • ·) (fun i => by aesop))).eigenvalues = 1 + c • hA.eigenvalues :=
  sorry

/--
> $$`\operatorname{eig}(\mathbf{A}-c\mathbf{I}) = \lambda_i - c \tag{286}`
-/
theorem eq_286 (A : Matrix n n ℝ) (hA : A.IsHermitian) (c : ℝ) :
    (hA.sub <| Matrix.isHermitian_diagonal fun _ => c).eigenvalues = hA.eigenvalues - Function.const _ c :=
  sorry

/--
> $$`\operatorname{eig}(\mathbf{A}^{-1}) = \lambda_i^{-1} \tag{287}`
-/
theorem eq_287 (A : Matrix n n ℝ) (hA : A.IsHermitian) :
    hA.inv.eigenvalues = hA.eigenvalues⁻¹ := by
  sorry

/--
> For a symmetric, positive matrix $`\mathbf{A}`,

  $$`\operatorname{eig}(\mathbf{A}^T\mathbf{A}) = \operatorname{eig}(\mathbf{A}\mathbf{A}^T) = \operatorname{eig}(\mathbf{A})\circ\operatorname{eig}(\mathbf{A}) \tag{288}`
-/
theorem eq_288 (A : Matrix n n ℝ) (hA : A.PosDef) :
    (A.isHermitian_conjTranspose_mul_self).eigenvalues = (A.isHermitian_mul_conjTranspose_self).eigenvalues ∧
    (A.isHermitian_mul_conjTranspose_self).eigenvalues = hA.isHermitian.eigenvalues^2 := by
  constructor
  · congr!
    · exact hA.isHermitian
    · exact hA.isHermitian.symm
  · sorry

/-!
### Characteristic polynomial
-/

/--
> The characteristic polynomial for the matrix $`\mathbf{A}` is

  $$`0 = \det(\mathbf{A}-\lambda\mathbf{I}) \tag{289}`
-/
theorem eq_289 (A : Matrix m m ℝ) (γ : ℝ) : (-A).charpoly.eval (-γ) = (A - Matrix.scalar _ γ).det := by
  rw [Matrix.eval_charpoly, map_neg, neg_sub_neg]

/--
> $$`= \lambda^n - g_1\lambda^{n-1} + g_2\lambda^{n-2} - ... + (-1)^n g_n \tag{290}`
-/
theorem eq_290 : (sorry : Prop) :=
  sorry

/-!
> Note that the coefficients $`g_j` for $`j = 1, ..., n` are the $`n` invariants under rotation of $`\mathbf{A}`. Thus, $`g_j` is the sum of the determinants of all the sub-matrices of $`\mathbf{A}` taken $`j` rows and columns at a time. That is, $`g_1` is the trace of $`\mathbf{A}`, and $`g_2` is the sum of the determinants of the $`n(n-1)/2` sub-matrices that can be formed from $`\mathbf{A}` by deleting all but two rows and columns, and so on – see \[17\].

## Singular Value Decomposition
-/

/--
> Any $`n\times m` matrix $`\mathbf{A}` can be written as

  $$`\mathbf{A} = \mathbf{U}\mathbf{D}\mathbf{V}^T, \tag{291}`
-/
theorem eq_291 : (sorry : Prop) :=
  sorry

/--
> where

  $$`\begin{array}{lcll} \mathbf{U} & = & \text{eigenvectors of } \mathbf{A}\mathbf{A}^T & n\times n \\ \mathbf{D} & = & \sqrt{\operatorname{diag}(\operatorname{eig}(\mathbf{A}\mathbf{A}^T))} & n\times m \\ \mathbf{V} & = & \text{eigenvectors of } \mathbf{A}^T\mathbf{A} & m\times m \end{array} \tag{292}`
-/
theorem eq_292 : (sorry : Prop) :=
  sorry

/-!
### Symmetric Square decomposed into squares
-/

/--
> Assume $`\mathbf{A}` to be $`n\times n` and symmetric. Then

  $$`\big[\ \mathbf{A}\ \big] = \big[\ \mathbf{V}\ \big]\big[\ \mathbf{D}\ \big]\big[\ \mathbf{V}^T\ \big], \tag{293}`
-/
theorem eq_293 : (sorry : Prop) :=
  sorry

/-!
> where $`\mathbf{D}` is diagonal with the eigenvalues of $`\mathbf{A}`, and $`\mathbf{V}` is orthogonal and the eigenvectors of $`\mathbf{A}`.

### Square decomposed into squares
-/

/--
> Assume $`\mathbf{A}\in\mathbb{R}^{n\times n}`. Then

  $$`\big[\ \mathbf{A}\ \big] = \big[\ \mathbf{V}\ \big]\big[\ \mathbf{D}\ \big]\big[\ \mathbf{U}^T\ \big], \tag{294}`
-/
theorem eq_294 : (sorry : Prop) :=
  sorry

/-!
> where $`\mathbf{D}` is diagonal with the square root of the eigenvalues of $`\mathbf{A}\mathbf{A}^T`, $`\mathbf{V}` is the eigenvectors of $`\mathbf{A}\mathbf{A}^T` and $`\mathbf{U}^T` is the eigenvectors of $`\mathbf{A}^T\mathbf{A}`.

### Square decomposed into rectangular
-/

/--
> Assume $`\mathbf{V}_*\mathbf{D}_*\mathbf{U}_*^T = \mathbf{0}` then we can expand the SVD of $`\mathbf{A}` into

  $$`\big[\ \mathbf{A}\ \big] = \left[\begin{array}{c|c} \mathbf{V} & \mathbf{V}_* \end{array}\right]\left[\begin{array}{c|c} \mathbf{D} & \mathbf{0} \\ \hline \mathbf{0} & \mathbf{D}_* \end{array}\right]\left[\begin{array}{c} \mathbf{U}^T \\ \hline \mathbf{U}_*^T \end{array}\right], \tag{295}`
-/
theorem eq_295 : (sorry : Prop) :=
  sorry

/-!
> where the SVD of $`\mathbf{A}` is $`\mathbf{A} = \mathbf{V}\mathbf{D}\mathbf{U}^T`.

### Rectangular decomposition I
-/

/--
> Assume $`\mathbf{A}` is $`n\times m`, $`\mathbf{V}` is $`n\times n`, $`\mathbf{D}` is $`n\times n`, $`\mathbf{U}^T` is $`n\times m`

  $$`\big[\quad\ \mathbf{A}\quad\ \big] = \big[\ \mathbf{V}\ \big]\big[\ \mathbf{D}\ \big]\big[\quad\ \mathbf{U}^T\quad\ \big], \tag{296}`
-/
theorem eq_296 : (sorry : Prop) :=
  sorry

/-!
> where $`\mathbf{D}` is diagonal with the square root of the eigenvalues of $`\mathbf{A}\mathbf{A}^T`, $`\mathbf{V}` is the eigenvectors of $`\mathbf{A}\mathbf{A}^T` and $`\mathbf{U}^T` is the eigenvectors of $`\mathbf{A}^T\mathbf{A}`.

### Rectangular decomposition II
-/

/--
> Assume $`\mathbf{A}` is $`n\times m`, $`\mathbf{V}` is $`n\times m`, $`\mathbf{D}` is $`m\times m`, $`\mathbf{U}^T` is $`m\times m`

  $$`\big[\quad\ \mathbf{A}\quad\ \big] = \big[\quad\ \mathbf{V}\quad\ \big]\left[\rule{0pt}{2.2em}\quad\ \mathbf{D}\quad\ \right]\left[\rule{0pt}{2.2em}\quad\ \mathbf{U}^T\quad\ \right] \tag{297}`
-/
theorem eq_297 : (sorry : Prop) :=
  sorry

/-!
### Rectangular decomposition III
-/

/--
> Assume $`\mathbf{A}` is $`n\times m`, $`\mathbf{V}` is $`n\times n`, $`\mathbf{D}` is $`n\times m`, $`\mathbf{U}^T` is $`m\times m`

  $$`\big[\quad\ \mathbf{A}\quad\ \big] = \big[\ \mathbf{V}\ \big]\big[\quad\ \mathbf{D}\quad\ \big]\left[\rule{0pt}{2.2em}\quad\ \mathbf{U}^T\quad\ \right], \tag{298}`
-/
theorem eq_298 : (sorry : Prop) :=
  sorry

/-!
> where $`\mathbf{D}` is diagonal with the square root of the eigenvalues of $`\mathbf{A}\mathbf{A}^T`, $`\mathbf{V}` is the eigenvectors of $`\mathbf{A}\mathbf{A}^T` and $`\mathbf{U}^T` is the eigenvectors of $`\mathbf{A}^T\mathbf{A}`.

## Triangular Decomposition

## LU decomposition
-/

/--
> Assume $`\mathbf{A}` is a square matrix with non-zero leading principal minors, then

  $$`\mathbf{A} = \mathbf{L}\mathbf{U} \tag{299}`
-/
theorem eq_299 : (sorry : Prop) :=
  sorry

/-!
> where $`\mathbf{L}` is a unique unit lower triangular matrix and $`\mathbf{U}` is a unique upper triangular matrix.

### Cholesky-decomposition
-/

/--
> Assume $`\mathbf{A}` is a symmetric positive definite square matrix, then

  $$`\mathbf{A} = \mathbf{U}^T\mathbf{U} = \mathbf{L}\mathbf{L}^T, \tag{300}`
-/
theorem eq_300 : (sorry : Prop) :=
  sorry

/-!
> where $`\mathbf{U}` is a unique upper triangular matrix and $`\mathbf{L}` is a lower triangular matrix.

## LDM decomposition
-/

/--
> Assume $`\mathbf{A}` is a square matrix with non-zero leading principal minors¹, then

  $$`\mathbf{A} = \mathbf{L}\mathbf{D}\mathbf{M}^T \tag{301}`
-/
theorem eq_301 : (sorry : Prop) :=
  sorry

/-!
> where $`\mathbf{L}, \mathbf{M}` are unique unit lower triangular matrices and $`\mathbf{D}` is a unique diagonal matrix.

## LDL decompositions
-/

/--
> The LDL decomposition are special cases of the LDM decomposition. Assume $`\mathbf{A}` is a non-singular symmetric definite square matrix, then

  $$`\mathbf{A} = \mathbf{L}\mathbf{D}\mathbf{L}^T = \mathbf{L}^T\mathbf{D}\mathbf{L} \tag{302}`
-/
theorem eq_302 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef) :
    A = LDL.lower hA * LDL.diag hA * (LDL.lower hA)ᴴ :=
  (LDL.lower_conj_diag hA).symm

/-!
> where $`\mathbf{L}` is a unit lower triangular matrix and $`\mathbf{D}` is a diagonal matrix. If $`\mathbf{A}` is also positive definite, then $`\mathbf{D}` has strictly positive diagonal entries.

  ¹ If the matrix that corresponds to a principal minor is a quadratic upper-left part of the larger matrix (i.e., it consists of matrix elements in rows and columns from 1 to k), then the principal minor is called a leading principal minor. For an n times n square matrix, there are n leading principal minors. \[31\]
-/

end MatrixCookbook
