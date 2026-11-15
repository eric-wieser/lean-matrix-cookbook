module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import MatrixCookbook.ForMathlib.Data.Matrix
public import MatrixCookbook.ForMathlib.Algebra.Invertible

set_option doc.verso true

/-!
# Inverses

## Basic

### Definition
-/

public section

namespace MatrixCookbook

variable {m n p : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

variable (A B C : Matrix n n ℂ)

open Matrix

open scoped Matrix BigOperators

/--
> The _inverse_ $`\mathbf{A}^{-1}` of a matrix $`\mathbf{A}\in\mathbb{C}^{n\times n}` is defined such that

  $$`\mathbf{A}\mathbf{A}^{-1} = \mathbf{A}^{-1}\mathbf{A} = \mathbf{I}, \tag{145}`
-/
theorem eq_145 (h : IsUnit A.det) : A * A⁻¹ = 1 ∧ A⁻¹ * A = 1 :=
  ⟨mul_nonsing_inv _ h, nonsing_inv_mul _ h⟩

-- mathlib has no need for this due to `eq_148`, but we include it for completeness
@[reducible, expose]
def cofactor {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) ℂ) :
    Matrix (Fin n.succ) (Fin n.succ) ℂ :=
  of fun i j : Fin n.succ => (-1) ^ (i + j : ℕ) * det (A.submatrix i.succAboveEmb j.succAboveEmb)

/-!
> where $`\mathbf{I}` is the $`n\times n` identity matrix. If $`\mathbf{A}^{-1}` exists, $`\mathbf{A}` is said to be _nonsingular_. Otherwise, $`\mathbf{A}` is said to be _singular_ (see e.g. \[12\]).

### Cofactors and Adjoint
-/

/--
> The _submatrix_ of a matrix $`\mathbf{A}`, denoted by $`[\mathbf{A}]_{ij}` is a $`(n-1)\times(n-1)` matrix obtained by deleting the $`i`th row and the $`j`th column of $`\mathbf{A}`. The $`(i,j)` _cofactor_ of a matrix is defined as

  $$`\operatorname{cof}(\mathbf{A},i,j) = (-1)^{i+j}\det([\mathbf{A}]_{ij}), \tag{146}`
-/
theorem eq_146 {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) ℂ) (i j : Fin n.succ) :
    cofactor A i j = (-1) ^ (i + j : ℕ) * det (A.submatrix i.succAboveEmb j.succAboveEmb) :=
  rfl

/--
> The _matrix of cofactors_ can be created from the cofactors

  $$`\operatorname{cof}(\mathbf{A}) = \begin{bmatrix} \operatorname{cof}(\mathbf{A},1,1) & \cdots & \operatorname{cof}(\mathbf{A},1,n) \\ \vdots & \operatorname{cof}(\mathbf{A},i,j) & \vdots \\ \operatorname{cof}(\mathbf{A},n,1) & \cdots & \operatorname{cof}(\mathbf{A},n,n) \end{bmatrix} \tag{147}`
-/
theorem eq_147 {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) ℂ) :
    cofactor A = of fun i j => cofactor A i j :=
  rfl

/--
> The _adjoint_ matrix is the transpose of the cofactor matrix

  $$`\operatorname{adj}(\mathbf{A}) = (\operatorname{cof}(\mathbf{A}))^T, \tag{148}`
-/
-- eq_147 is a trivial matrix definiton!
theorem eq_148 {n : ℕ} (A : Matrix (Fin n.succ) (Fin n.succ) ℂ) : adjugate A = (cofactor A)ᵀ :=
  Matrix.ext <| adjugate_fin_succ_eq_det_submatrix _

/-!
### Determinant
-/

/--
> The _determinant_ of a matrix $`\mathbf{A}\in\mathbb{C}^{n\times n}` is defined as (see \[12\])

  $$`\det(\mathbf{A}) = \sum_{j=1}^n(-1)^{j+1}A_{1j}\det([\mathbf{A}]_{1j}) \tag{149}`

Note: adapted from column 0 to column 1.
-/
theorem eq_149 (n : ℕ) (A : Matrix (Fin n.succ) (Fin n.succ) ℂ) :
    det A = ∑ i : Fin n.succ, (-1) ^ (i : ℕ) * A i 0 * det (A.submatrix i.succAboveEmb Fin.succ) :=
  det_succ_column_zero _

/--
> $$`= \sum_{j=1}^n A_{1j}\operatorname{cof}(\mathbf{A},1,j). \tag{150}`
-/
theorem eq_150 (n : ℕ) (A : Matrix (Fin n.succ) (Fin n.succ) ℂ) :
    det A = ∑ j : Fin n.succ, A 0 j * adjugate A j 0 :=
  det_eq_sum_mul_adjugate_row _ _

/-!
### Construction
-/

/--
> The inverse matrix can be constructed, using the adjoint matrix, by

  $$`\mathbf{A}^{-1} = \frac{1}{\det(\mathbf{A})}\cdot\operatorname{adj}(\mathbf{A}) \tag{151}`
-/
theorem eq_151 : A⁻¹ = (1 / A.det) • adjugate A := by rw [inv_def, Ring.inverse_eq_inv, one_div]

/-!
> For the case of $`2\times 2` matrices, see section 1.3.

### Condition number
-/

/--
> The condition number of a matrix $`c(\mathbf{A})` is the ratio between the largest and the smallest singular value of a matrix (see Section 5.3 on singular values),

  $$`c(\mathbf{A}) = \frac{d_+}{d_-} \tag{152}`
-/
theorem eq_152 : (sorry : Prop) :=
  sorry

/--
> The condition number can be used to measure how singular a matrix is. If the condition number is large, it indicates that the matrix is nearly singular. The condition number can also be estimated from the matrix norms. Here

  $$`c(\mathbf{A}) = \|\mathbf{A}\|\cdot\|\mathbf{A}^{-1}\|, \tag{153}`
-/
theorem eq_153 : (sorry : Prop) :=
  sorry

/-!
> where $`\|\cdot\|` is a norm such as e.g the 1-norm, the 2-norm, the $`\infty`-norm or the Frobenius norm (see Sec 10.4 for more on matrix norms).
-/

/--
> The 2-norm of $`\mathbf{A}` equals $`\sqrt{(\max(\operatorname{eig}(\mathbf{A}^H\mathbf{A})))}` \[12, p.57\]. For a symmetric matrix, this reduces to $`||\mathbf{A}||_2 = \max(|\operatorname{eig}(\mathbf{A})|)` \[12, p.394\]. If the matrix is symmetric and positive definite, $`||\mathbf{A}||_2 = \max(\operatorname{eig}(\mathbf{A}))`. The condition number based on the 2-norm thus reduces to

  $$`\|\mathbf{A}\|_2\|\mathbf{A}^{-1}\|_2 = \max(\operatorname{eig}(\mathbf{A}))\max(\operatorname{eig}(\mathbf{A}^{-1})) = \frac{\max(\operatorname{eig}(\mathbf{A}))}{\min(\operatorname{eig}(\mathbf{A}))}. \tag{154}`
-/
theorem eq_154 : (sorry : Prop) :=
  sorry

/-!
## Exact Relations

### Basic
-/

/--
> $$`(\mathbf{A}\mathbf{B})^{-1} = \mathbf{B}^{-1}\mathbf{A}^{-1} \tag{155}`
-/
theorem eq_155 (A B : Matrix m m ℂ) : (A * B)⁻¹ = B⁻¹ * A⁻¹ :=
  mul_inv_rev _ _

/-!
### The Woodbury identity
-/

/--
> The Woodbury identity comes in many variants. The latter of the two can be found in \[12\]

  $$`(\mathbf{A}+\mathbf{C}\mathbf{B}\mathbf{C}^T)^{-1} = \mathbf{A}^{-1} - \mathbf{A}^{-1}\mathbf{C}(\mathbf{B}^{-1}+\mathbf{C}^T\mathbf{A}^{-1}\mathbf{C})^{-1}\mathbf{C}^T\mathbf{A}^{-1} \tag{156}`
-/
theorem eq_156
    (A : Matrix n n ℂ) (B : Matrix m m ℂ) (C : Matrix n m ℂ)
    (hA : IsUnit A) (hB : IsUnit B) (h : IsUnit (B⁻¹ + Cᵀ*A⁻¹*C)) :
    (A + C * B * Cᵀ)⁻¹ = A⁻¹ - A⁻¹ * C * (B⁻¹ + Cᵀ*A⁻¹*C)⁻¹ * Cᵀ * A⁻¹ :=
  Matrix.add_mul_mul_inv_eq_sub _ _ _ _ hA hB h

/--
> $$`(\mathbf{A}+\mathbf{U}\mathbf{B}\mathbf{V})^{-1} = \mathbf{A}^{-1} - \mathbf{A}^{-1}\mathbf{U}(\mathbf{B}^{-1}+\mathbf{V}\mathbf{A}^{-1}\mathbf{U})^{-1}\mathbf{V}\mathbf{A}^{-1} \tag{157}`
-/
theorem eq_157 (A : Matrix n n ℂ) (B : Matrix m m ℂ) (U : Matrix n m ℂ) (V : Matrix m n ℂ)
    (hA : IsUnit A) (hB : IsUnit B) (h : IsUnit (B⁻¹ + V*A⁻¹*U)) :
    (A + U * B * V)⁻¹ = A⁻¹ - A⁻¹ * U * (B⁻¹ + V*A⁻¹*U)⁻¹ * V * A⁻¹ :=
  Matrix.add_mul_mul_inv_eq_sub _ _ _ _ hA hB h

section

open scoped ComplexOrder

/--
> If $`\mathbf{P},\mathbf{R}` are positive definite, then (see \[30\])

  $$`(\mathbf{P}^{-1}+\mathbf{B}^T\mathbf{R}^{-1}\mathbf{B})^{-1}\mathbf{B}^T\mathbf{R}^{-1} = \mathbf{P}\mathbf{B}^T(\mathbf{B}\mathbf{P}\mathbf{B}^T+\mathbf{R})^{-1} \tag{158}`

Note that this has been generalized from the {lit}`ℝ`/{lit}`ᵀ` in the source to {lit}`ℂ`/{lit}`ᴴ`.
-/
theorem eq_158 (P : Matrix n n ℂ) (R : Matrix m m ℂ) (B : Matrix m n ℂ)
    (hP : P.PosDef) (hR : R.PosDef) :
    (P⁻¹ + Bᴴ * R⁻¹ * B)⁻¹ * Bᴴ * R⁻¹ = P * Bᴴ * (B * P * Bᴴ + R)⁻¹ := by
  let : Invertible P := hP.isUnit.invertible
  let : Invertible R := hR.isUnit.invertible
  let : Invertible (R + B*P*Bᴴ) :=
    (hR.add_posSemidef <| hP.posSemidef.mul_mul_conjTranspose_same B).isUnit.invertible
  rw [Matrix.add_mul_mul_inv_eq_sub, add_comm _ R]
  · simp_rw [Matrix.inv_inv_of_invertible, Matrix.sub_mul, Matrix.mul_assoc, ← Matrix.mul_sub]
    congr 2
    simp_rw [← Matrix.mul_assoc]
    refine hR.isUnit.isRegular.right ?_
    simp_rw [Matrix.sub_mul, sub_eq_iff_eq_add, Matrix.mul_assoc, ← Matrix.mul_add,
      ← Matrix.mul_assoc, Matrix.inv_mul_cancel_right_of_invertible,
      Matrix.inv_mul_of_invertible]
  · simpa only [isUnit_nonsing_inv_iff] using hP.isUnit
  · simpa only [isUnit_nonsing_inv_iff] using hR.isUnit
  · simp_rw [Matrix.inv_inv_of_invertible]
    exact isUnit_of_invertible _

end

/-!
### The Kailath Variant
-/

/--
> $$`(\mathbf{A}+\mathbf{B}\mathbf{C})^{-1} = \mathbf{A}^{-1} - \mathbf{A}^{-1}\mathbf{B}(\mathbf{I}+\mathbf{C}\mathbf{A}^{-1}\mathbf{B})^{-1}\mathbf{C}\mathbf{A}^{-1} \tag{159}`
-/
theorem eq_159 (B : Matrix n m ℂ) (C : Matrix m n ℂ)
    (hA : IsUnit A) (h : IsUnit (1 + C * A⁻¹ * B)) :
    (A + B * C)⁻¹ = A⁻¹ - A⁻¹ * B * (1 + C * A⁻¹ * B)⁻¹ * C * A⁻¹ := by
  have := Matrix.add_mul_mul_inv_eq_sub A B _ C hA isUnit_one (by simpa using h)
  simpa using this

/-!
> See \[4, page 153\].

### Sherman-Morrison
-/

/--
> $$`(\mathbf{A}+\mathbf{b}\mathbf{c}^T)^{-1} = \mathbf{A}^{-1} - \frac{\mathbf{A}^{-1}\mathbf{b}\mathbf{c}^T\mathbf{A}^{-1}}{1+\mathbf{c}^T\mathbf{A}^{-1}\mathbf{b}} \tag{160}`
-/
theorem eq_160 (b c : n → ℂ) (hA : IsUnit A) (h : 1 + c ⬝ᵥ A⁻¹ *ᵥ b ≠ 0) :
    (A + replicateCol Unit b * replicateRow Unit c)⁻¹ = A⁻¹ - (1 + c ⬝ᵥ A⁻¹ *ᵥ b)⁻¹ • A⁻¹ * (replicateCol Unit b * replicateRow Unit c) * A⁻¹ := by
  rw [eq_159 _ _ _ hA, ← Matrix.mul_assoc _ (replicateCol Unit b), Matrix.mul_assoc _ (replicateRow Unit c), Matrix.mul_assoc _ (replicateRow Unit c),
    Matrix.smul_mul]
  · congr
    rw [← replicateCol_mulVec, ← replicateRow_vecMul, replicateRow_mul_replicateCol, smul_eq_mul_diagonal,
      Matrix.inv_subsingleton (m := Unit)]
    simp_rw [Ring.inverse_eq_inv]
    simp [← dotProduct_mulVec]
  · rw [isUnit_iff_isUnit_det, det_unique, Matrix.add_apply, one_apply_eq]
    rw [← replicateCol_mulVec, ← replicateRow_vecMul, replicateRow_mulVec_eq_const, ← dotProduct_mulVec, isUnit_iff_ne_zero]
    exact h

/-!
### The Searle Set of Identities
-/

/--
> The following set of identities, can be found in \[25, page 151\],

  $$`(\mathbf{I}+\mathbf{A}^{-1})^{-1} = \mathbf{A}(\mathbf{A}+\mathbf{I})^{-1} \tag{161}`
-/
theorem eq_161 : (1 + A⁻¹)⁻¹ = A * (A + 1)⁻¹ :=
  sorry

/--
> $$`(\mathbf{A}+\mathbf{B}\mathbf{B}^T)^{-1}\mathbf{B} = \mathbf{A}^{-1}\mathbf{B}(\mathbf{I}+\mathbf{B}^T\mathbf{A}^{-1}\mathbf{B})^{-1} \tag{162}`
-/
theorem eq_162 : (A + Bᵀ * B)⁻¹ * B = A⁻¹ * B * (1 + Bᵀ * A⁻¹ * B)⁻¹ :=
  sorry

/--
> $$`(\mathbf{A}^{-1}+\mathbf{B}^{-1})^{-1} = \mathbf{A}(\mathbf{A}+\mathbf{B})^{-1}\mathbf{B} = \mathbf{B}(\mathbf{A}+\mathbf{B})^{-1}\mathbf{A} \tag{163}`
-/
theorem eq_163 (hA : IsUnit A) (hB : IsUnit B) :
    (A⁻¹ + B⁻¹)⁻¹ = A * (A + B)⁻¹ * B ∧ (A⁻¹ + B⁻¹)⁻¹ = B * (A + B)⁻¹ * A := by
  let := hA.invertible; let := hB.invertible
  conv_lhs => rw [add_comm]
  rw [Matrix.inv_add_inv (iff_of_true hA hB), Matrix.inv_add_inv (iff_of_true hB hA)]
  simp_rw [Matrix.mul_inv_rev, Matrix.inv_inv_of_invertible, mul_assoc, add_comm]
  simp

/--
> $$`\mathbf{A} - \mathbf{A}(\mathbf{A}+\mathbf{B})^{-1}\mathbf{A} = \mathbf{B} - \mathbf{B}(\mathbf{A}+\mathbf{B})^{-1}\mathbf{B} \tag{164}`
-/
theorem eq_164 : A - A * (A + B)⁻¹ * A = B - B * (A + B)⁻¹ * B :=
  sorry

/--
> $$`\mathbf{A}^{-1}+\mathbf{B}^{-1} = \mathbf{A}^{-1}(\mathbf{A}+\mathbf{B})\mathbf{B}^{-1} \tag{165}`
-/
theorem eq_165 (hA : IsUnit A) (hB : IsUnit B) : A⁻¹ + B⁻¹ = A⁻¹ * (A + B) * B⁻¹ :=
  Matrix.inv_add_inv <| iff_of_true hA hB

/--
> $$`(\mathbf{I}+\mathbf{A}\mathbf{B})^{-1} = \mathbf{I} - \mathbf{A}(\mathbf{I}+\mathbf{B}\mathbf{A})^{-1}\mathbf{B} \tag{166}`
-/
theorem eq_166 : (1 + A * B)⁻¹ = 1 - A * (1 + B * A)⁻¹ * B :=
  sorry

/--
> $$`(\mathbf{I}+\mathbf{A}\mathbf{B})^{-1}\mathbf{A} = \mathbf{A}(\mathbf{I}+\mathbf{B}\mathbf{A})^{-1} \tag{167}`
-/
theorem eq_167 : (1 + A * B)⁻¹ * A = A * (1 + B * A)⁻¹ :=
  sorry

/-!
### Rank-1 update of inverse of inner product

> Denote $`\mathbf{A} = (\mathbf{X}^T\mathbf{X})^{-1}` and that $`\mathbf{X}` is extended to include a new column vector in the end $`\tilde{\mathbf{X}} = [\mathbf{X}\ \ \mathbf{v}]`. Then \[34\]

  $$`(\tilde{\mathbf{X}}^T\tilde{\mathbf{X}})^{-1} = \begin{bmatrix} \mathbf{A} + \frac{\mathbf{A}\mathbf{X}^T\mathbf{v}\mathbf{v}^T\mathbf{X}\mathbf{A}^T}{\mathbf{v}^T\mathbf{v}-\mathbf{v}^T\mathbf{X}\mathbf{A}\mathbf{X}^T\mathbf{v}} & \frac{-\mathbf{A}\mathbf{X}^T\mathbf{v}}{\mathbf{v}^T\mathbf{v}-\mathbf{v}^T\mathbf{X}\mathbf{A}\mathbf{X}^T\mathbf{v}} \\ \frac{-\mathbf{v}^T\mathbf{X}\mathbf{A}^T}{\mathbf{v}^T\mathbf{v}-\mathbf{v}^T\mathbf{X}\mathbf{A}\mathbf{X}^T\mathbf{v}} & \frac{1}{\mathbf{v}^T\mathbf{v}-\mathbf{v}^T\mathbf{X}\mathbf{A}\mathbf{X}^T\mathbf{v}} \end{bmatrix}`

### Rank-1 update of Moore-Penrose Inverse
-/

/--
> The following is a rank-1 update for the Moore-Penrose pseudo-inverse of real valued matrices and proof can be found in \[18\]. The matrix $`\mathbf{G}` is defined below:

  $$`(\mathbf{A}+\mathbf{c}\mathbf{d}^T)^+ = \mathbf{A}^+ + \mathbf{G} \tag{168}`
-/
theorem eq_168 : (sorry : Prop) :=
  sorry

/--
> Using the the notation

  $$`\beta = 1 + \mathbf{d}^T\mathbf{A}^+\mathbf{c} \tag{169}`
-/
theorem eq_169 : (sorry : Prop) :=
  sorry

/--
> $$`\mathbf{v} = \mathbf{A}^+\mathbf{c} \tag{170}`
-/
theorem eq_170 : (sorry : Prop) :=
  sorry

/--
> $$`\mathbf{n} = (\mathbf{A}^+)^T\mathbf{d} \tag{171}`
-/
theorem eq_171 : (sorry : Prop) :=
  sorry

/--
> $$`\mathbf{w} = (\mathbf{I}-\mathbf{A}\mathbf{A}^+)\mathbf{c} \tag{172}`
-/
theorem eq_172 : (sorry : Prop) :=
  sorry

/--
> $$`\mathbf{m} = (\mathbf{I}-\mathbf{A}^+\mathbf{A})^T\mathbf{d} \tag{173}`
-/
theorem eq_173 : (sorry : Prop) :=
  sorry

/-!
> the solution is given as six different cases, depending on the entities $`||\mathbf{w}||`, $`||\mathbf{m}||`, and $`\beta`. Please note, that for any (column) vector $`\mathbf{v}` it holds that $`\mathbf{v}^+ = \mathbf{v}^T(\mathbf{v}^T\mathbf{v})^{-1} = \frac{\mathbf{v}^T}{||\mathbf{v}||^2}`. The solution is:
-/

/--
> Case 1 of 6: If $`||\mathbf{w}|| \neq 0` and $`||\mathbf{m}|| \neq 0`. Then

  $$`\mathbf{G} = -\mathbf{v}\mathbf{w}^+ - (\mathbf{m}^+)^T\mathbf{n}^T + \beta(\mathbf{m}^+)^T\mathbf{w}^+ \tag{174}`
-/
theorem eq_174 : (sorry : Prop) :=
  sorry

/--
> $$`= -\frac{1}{||\mathbf{w}||^2}\mathbf{v}\mathbf{w}^T - \frac{1}{||\mathbf{m}||^2}\mathbf{m}\mathbf{n}^T + \frac{\beta}{||\mathbf{m}||^2||\mathbf{w}||^2}\mathbf{m}\mathbf{w}^T \tag{175}`
-/
theorem eq_175 : (sorry : Prop) :=
  sorry

/--
> Case 2 of 6: If $`||\mathbf{w}|| = 0` and $`||\mathbf{m}|| \neq 0` and $`\beta = 0`. Then

  $$`\mathbf{G} = -\mathbf{v}\mathbf{v}^+\mathbf{A}^+ - (\mathbf{m}^+)^T\mathbf{n}^T \tag{176}`
-/
theorem eq_176 : (sorry : Prop) :=
  sorry

/--
> $$`= -\frac{1}{||\mathbf{v}||^2}\mathbf{v}\mathbf{v}^T\mathbf{A}^+ - \frac{1}{||\mathbf{m}||^2}\mathbf{m}\mathbf{n}^T \tag{177}`
-/
theorem eq_177 : (sorry : Prop) :=
  sorry

/--
> Case 3 of 6: If $`||\mathbf{w}|| = 0` and $`\beta \neq 0`. Then

  $$`\mathbf{G} = \frac{1}{\beta}\mathbf{m}\mathbf{v}^T\mathbf{A}^+ - \frac{\beta}{||\mathbf{v}||^2||\mathbf{m}||^2+|\beta|^2}\left(\frac{||\mathbf{v}||^2}{\beta}\mathbf{m}+\mathbf{v}\right)\left(\frac{||\mathbf{m}||^2}{\beta}(\mathbf{A}^+)^T\mathbf{v}+\mathbf{n}\right)^T \tag{178}`
-/
theorem eq_178 : (sorry : Prop) :=
  sorry

/--
> Case 4 of 6: If $`||\mathbf{w}|| \neq 0` and $`||\mathbf{m}|| = 0` and $`\beta = 0`. Then

  $$`\mathbf{G} = -\mathbf{A}^+\mathbf{n}\mathbf{n}^+ - \mathbf{v}\mathbf{w}^+ \tag{179}`
-/
theorem eq_179 : (sorry : Prop) :=
  sorry

/--
> $$`= -\frac{1}{||\mathbf{n}||^2}\mathbf{A}^+\mathbf{n}\mathbf{n}^T - \frac{1}{||\mathbf{w}||^2}\mathbf{v}\mathbf{w}^T \tag{180}`
-/
theorem eq_180 : (sorry : Prop) :=
  sorry

/--
> Case 5 of 6: If $`||\mathbf{m}|| = 0` and $`\beta \neq 0`. Then

  $$`\mathbf{G} = \frac{1}{\beta}\mathbf{A}^+\mathbf{n}\mathbf{w}^T - \frac{\beta}{||\mathbf{n}||^2||\mathbf{w}||^2+|\beta|^2}\left(\frac{||\mathbf{w}||^2}{\beta}\mathbf{A}^+\mathbf{n}+\mathbf{v}\right)\left(\frac{||\mathbf{n}||^2}{\beta}\mathbf{w}+\mathbf{n}\right)^T \tag{181}`
-/
theorem eq_181 : (sorry : Prop) :=
  sorry

/--
> Case 6 of 6: If $`||\mathbf{w}|| = 0` and $`||\mathbf{m}|| = 0` and $`\beta = 0`. Then

  $$`\mathbf{G} = -\mathbf{v}\mathbf{v}^+\mathbf{A}^+ - \mathbf{A}^+\mathbf{n}\mathbf{n}^+ + \mathbf{v}^+\mathbf{A}^+\mathbf{n}\mathbf{v}\mathbf{n}^+ \tag{182}`
-/
theorem eq_182 : (sorry : Prop) :=
  sorry

/--
> $$`= -\frac{1}{||\mathbf{v}||^2}\mathbf{v}\mathbf{v}^T\mathbf{A}^+ - \frac{1}{||\mathbf{n}||^2}\mathbf{A}^+\mathbf{n}\mathbf{n}^T + \frac{\mathbf{v}^T\mathbf{A}^+\mathbf{n}}{||\mathbf{v}||^2||\mathbf{n}||^2}\mathbf{v}\mathbf{n}^T \tag{183}`
-/
theorem eq_183 : (sorry : Prop) :=
  sorry

/-!
## Implication on Inverses
-/

/--
> $$`\text{If}\qquad (\mathbf{A}+\mathbf{B})^{-1} = \mathbf{A}^{-1}+\mathbf{B}^{-1} \qquad \text{then} \qquad \mathbf{A}\mathbf{B}^{-1}\mathbf{A} = \mathbf{B}\mathbf{A}^{-1}\mathbf{B} \tag{184}`
-/
theorem eq_184 (h_A : IsUnit A) (h_B : IsUnit B) (h_A_B : IsUnit (A + B)) (h : (A + B)⁻¹ = A⁻¹ + B⁻¹) :
    A * B⁻¹ * A = B * A⁻¹ * B := by
  let : Invertible A := h_A.invertible
  let : Invertible B := h_B.invertible
  let : Invertible (A + B) := h_A_B.invertible
  simp_rw [← Matrix.invOf_eq_nonsing_inv] at *
  exact eq_of_invOf_add_eq_invOf_add_invOf h

/-!
> See \[25\].

### A PosDef identity
-/

/--
> Assume $`\mathbf{P},\mathbf{R}` to be positive definite and invertible, then

  $$`(\mathbf{P}^{-1}+\mathbf{B}^T\mathbf{R}^{-1}\mathbf{B})^{-1}\mathbf{B}^T\mathbf{R}^{-1} = \mathbf{P}\mathbf{B}^T(\mathbf{B}\mathbf{P}\mathbf{B}^T+\mathbf{R})^{-1} \tag{185}`
-/
theorem eq_185 : (sorry : Prop) :=
  sorry

/-!
> See \[30\].

## Approximations
-/

/--
> The following identity is known as the _Neuman series_ of a matrix, which holds when $`|\lambda_i| < 1` for all eigenvalues $`\lambda_i`

  $$`(\mathbf{I}-\mathbf{A})^{-1} = \sum_{n=0}^\infty\mathbf{A}^n \tag{186}`
-/
theorem eq_186 : (sorry : Prop) :=
  sorry

/--
> which is equivalent to

  $$`(\mathbf{I}+\mathbf{A})^{-1} = \sum_{n=0}^\infty(-1)^n\mathbf{A}^n \tag{187}`
-/
theorem eq_187 : (sorry : Prop) :=
  sorry

/--
> When $`|\lambda_i| < 1` for all eigenvalues $`\lambda_i`, it holds that $`\mathbf{A}\rightarrow 0` for $`n\rightarrow\infty`, and the following approximations holds

  $$`(\mathbf{I}-\mathbf{A})^{-1} \cong \mathbf{I}+\mathbf{A}+\mathbf{A}^2 \tag{188}`
-/
theorem eq_188 : (sorry : Prop) :=
  sorry

/--
> $$`(\mathbf{I}+\mathbf{A})^{-1} \cong \mathbf{I}-\mathbf{A}+\mathbf{A}^2 \tag{189}`
-/
theorem eq_189 : (sorry : Prop) :=
  sorry

/--
> The following approximation is from \[22\] and holds when $`\mathbf{A}` large and symmetric

  $$`\mathbf{A}-\mathbf{A}(\mathbf{I}+\mathbf{A})^{-1}\mathbf{A} \cong \mathbf{I}-\mathbf{A}^{-1} \tag{190}`
-/
theorem eq_190 : (sorry : Prop) :=
  sorry

/--
> If $`\sigma^2` is small compared to $`\mathbf{Q}` and $`\mathbf{M}` then

  $$`(\mathbf{Q}+\sigma^2\mathbf{M})^{-1} \cong \mathbf{Q}^{-1} - \sigma^2\mathbf{Q}^{-1}\mathbf{M}\mathbf{Q}^{-1} \tag{191}`
-/
theorem eq_191 : (sorry : Prop) :=
  sorry

/--
> Proof:

  $$`(\mathbf{Q}+\sigma^2\mathbf{M})^{-1} = \tag{192}`
-/
theorem eq_192 : (sorry : Prop) :=
  sorry

/--
> $$`(\mathbf{Q}\mathbf{Q}^{-1}\mathbf{Q}+\sigma^2\mathbf{M}\mathbf{Q}^{-1}\mathbf{Q})^{-1} = \tag{193}`
-/
theorem eq_193 : (sorry : Prop) :=
  sorry

/--
> $$`((\mathbf{I}+\sigma^2\mathbf{M}\mathbf{Q}^{-1})\mathbf{Q})^{-1} = \tag{194}`
-/
theorem eq_194 : (sorry : Prop) :=
  sorry

/--
> $$`\mathbf{Q}^{-1}(\mathbf{I}+\sigma^2\mathbf{M}\mathbf{Q}^{-1})^{-1} \tag{195}`
-/
theorem eq_195 : (sorry : Prop) :=
  sorry

/--
> This can be rewritten using the Taylor expansion:

  $$`\mathbf{Q}^{-1}(\mathbf{I}+\sigma^2\mathbf{M}\mathbf{Q}^{-1})^{-1} = \tag{196}`
-/
theorem eq_196 : (sorry : Prop) :=
  sorry

/--
> $$`\mathbf{Q}^{-1}(\mathbf{I}-\sigma^2\mathbf{M}\mathbf{Q}^{-1}+(\sigma^2\mathbf{M}\mathbf{Q}^{-1})^2-...) \cong \mathbf{Q}^{-1}-\sigma^2\mathbf{Q}^{-1}\mathbf{M}\mathbf{Q}^{-1} \tag{197}`
-/
theorem eq_197 : (sorry : Prop) :=
  sorry

/-!
## Generalized Inverse

### Definition
-/

/--
> A generalized inverse matrix of the matrix $`\mathbf{A}` is any matrix $`\mathbf{A}^-` such that (see \[26\])

  $$`\mathbf{A}\mathbf{A}^-\mathbf{A} = \mathbf{A} \tag{198}`
-/
theorem eq_198 : (sorry : Prop) :=
  sorry

/-!
> The matrix $`\mathbf{A}^-` is not unique.

## Pseudo Inverse

### Definition

> The pseudo inverse (or Moore-Penrose inverse) of a matrix $`\mathbf{A}` is the matrix $`\mathbf{A}^+` that fulfils

  $$`\begin{array}{ll} \text{I} & \mathbf{A}\mathbf{A}^+\mathbf{A} = \mathbf{A} \\ \text{II} & \mathbf{A}^+\mathbf{A}\mathbf{A}^+ = \mathbf{A}^+ \\ \text{III} & \mathbf{A}\mathbf{A}^+ \text{ symmetric} \\ \text{IV} & \mathbf{A}^+\mathbf{A} \text{ symmetric} \end{array}`

  The matrix $`\mathbf{A}^+` is unique and does always exist. Note that in case of complex matrices, the symmetric condition is substituted by a condition of being Hermitian.

### Properties
-/

/--
> Assume $`\mathbf{A}^+` to be the pseudo-inverse of $`\mathbf{A}`, then (See \[3\] for some of them)

  $$`(\mathbf{A}^+)^+ = \mathbf{A} \tag{199}`
-/
theorem eq_199 : (sorry : Prop) :=
  sorry

/--
> $$`(\mathbf{A}^T)^+ = (\mathbf{A}^+)^T \tag{200}`
-/
theorem eq_200 : (sorry : Prop) :=
  sorry

/--
> $$`(\mathbf{A}^H)^+ = (\mathbf{A}^+)^H \tag{201}`
-/
theorem eq_201 : (sorry : Prop) :=
  sorry

/--
> $$`(\mathbf{A}^*)^+ = (A^+)^* \tag{202}`
-/
theorem eq_202 : (sorry : Prop) :=
  sorry

/--
> $$`(\mathbf{A}^+\mathbf{A})\mathbf{A}^H = \mathbf{A}^H \tag{203}`
-/
theorem eq_203 : (sorry : Prop) :=
  sorry

/--
> $$`(\mathbf{A}^+\mathbf{A})\mathbf{A}^T \neq \mathbf{A}^T \tag{204}`
-/
theorem eq_204 : (sorry : Prop) :=
  sorry

/--
> $$`(c\mathbf{A})^+ = (1/c)\mathbf{A}^+ \tag{205}`
-/
theorem eq_205 : (sorry : Prop) :=
  sorry

/--
> $$`\mathbf{A}^+ = (\mathbf{A}^T\mathbf{A})^+\mathbf{A}^T \tag{206}`
-/
theorem eq_206 : (sorry : Prop) :=
  sorry

/--
> $$`\mathbf{A}^+ = \mathbf{A}^T(\mathbf{A}\mathbf{A}^T)^+ \tag{207}`
-/
theorem eq_207 : (sorry : Prop) :=
  sorry

/--
> $$`(\mathbf{A}^T\mathbf{A})^+ = \mathbf{A}^+(\mathbf{A}^T)^+ \tag{208}`
-/
theorem eq_208 : (sorry : Prop) :=
  sorry

/--
> $$`(\mathbf{A}\mathbf{A}^T)^+ = (\mathbf{A}^T)^+\mathbf{A}^+ \tag{209}`
-/
theorem eq_209 : (sorry : Prop) :=
  sorry

/--
> $$`\mathbf{A}^+ = (\mathbf{A}^H\mathbf{A})^+\mathbf{A}^H \tag{210}`
-/
theorem eq_210 : (sorry : Prop) :=
  sorry

/--
> $$`\mathbf{A}^+ = \mathbf{A}^H(\mathbf{A}\mathbf{A}^H)^+ \tag{211}`
-/
theorem eq_211 : (sorry : Prop) :=
  sorry

/--
> $$`(\mathbf{A}^H\mathbf{A})^+ = \mathbf{A}^+(\mathbf{A}^H)^+ \tag{212}`
-/
theorem eq_212 : (sorry : Prop) :=
  sorry

/--
> $$`(\mathbf{A}\mathbf{A}^H)^+ = (\mathbf{A}^H)^+\mathbf{A}^+ \tag{213}`
-/
theorem eq_213 : (sorry : Prop) :=
  sorry

/--
> $$`(\mathbf{A}\mathbf{B})^+ = (\mathbf{A}^+\mathbf{A}\mathbf{B})^+(\mathbf{A}\mathbf{B}\mathbf{B}^+)^+ \tag{214}`
-/
theorem eq_214 : (sorry : Prop) :=
  sorry

/--
> $$`f(\mathbf{A}^H\mathbf{A}) - f(0)\mathbf{I} = \mathbf{A}^+[f(\mathbf{A}\mathbf{A}^H) - f(0)\mathbf{I}]\mathbf{A} \tag{215}`
-/
theorem eq_215 : (sorry : Prop) :=
  sorry

/--
> $$`f(\mathbf{A}\mathbf{A}^H) - f(0)\mathbf{I} = \mathbf{A}[f(\mathbf{A}^H\mathbf{A}) - f(0)\mathbf{I}]\mathbf{A}^+ \tag{216}`
-/
theorem eq_216 : (sorry : Prop) :=
  sorry

/-!
> where $`\mathbf{A}\in\mathbb{C}^{n\times m}`.
-/

/--
> Assume $`\mathbf{A}` to have full rank, then

  $$`(\mathbf{A}\mathbf{A}^+)(\mathbf{A}\mathbf{A}^+) = \mathbf{A}\mathbf{A}^+ \tag{217}`
-/
theorem eq_217 : (sorry : Prop) :=
  sorry

/--
> $$`(\mathbf{A}^+\mathbf{A})(\mathbf{A}^+\mathbf{A}) = \mathbf{A}^+\mathbf{A} \tag{218}`
-/
theorem eq_218 : (sorry : Prop) :=
  sorry

/--
> $$`\operatorname{Tr}(\mathbf{A}\mathbf{A}^+) = \operatorname{rank}(\mathbf{A}\mathbf{A}^+) \qquad (\text{See [26]}) \tag{219}`
-/
theorem eq_219 : (sorry : Prop) :=
  sorry

/--
> $$`\operatorname{Tr}(\mathbf{A}^+\mathbf{A}) = \operatorname{rank}(\mathbf{A}^+\mathbf{A}) \qquad (\text{See [26]}) \tag{220}`
-/
theorem eq_220 : (sorry : Prop) :=
  sorry

/--
> For two matrices it hold that

  $$`(\mathbf{A}\mathbf{B})^+ = (\mathbf{A}^+\mathbf{A}\mathbf{B})^+(\mathbf{A}\mathbf{B}\mathbf{B}^+)^+ \tag{221}`
-/
theorem eq_221 : (sorry : Prop) :=
  sorry

/--
> $$`(\mathbf{A}\otimes\mathbf{B})^+ = \mathbf{A}^+\otimes\mathbf{B}^+ \tag{222}`
-/
theorem eq_222 : (sorry : Prop) :=
  sorry

/-!
### Construction

> Assume that $`\mathbf{A}` has full rank, then

  $$`\begin{array}{llll} \mathbf{A}\ n\times n & \text{Square} & \operatorname{rank}(\mathbf{A}) = n & \Rightarrow\quad \mathbf{A}^+ = \mathbf{A}^{-1} \\ \mathbf{A}\ n\times m & \text{Broad} & \operatorname{rank}(\mathbf{A}) = n & \Rightarrow\quad \mathbf{A}^+ = \mathbf{A}^T(\mathbf{A}\mathbf{A}^T)^{-1} \\ \mathbf{A}\ n\times m & \text{Tall} & \operatorname{rank}(\mathbf{A}) = m & \Rightarrow\quad \mathbf{A}^+ = (\mathbf{A}^T\mathbf{A})^{-1}\mathbf{A}^T \end{array}`

  The so-called "broad version" is also known as _right inverse_ and the "tall version" as the _left inverse_.
-/

/--
> Assume $`\mathbf{A}` does not have full rank, i.e. $`\mathbf{A}` is $`n\times m` and $`\operatorname{rank}(\mathbf{A}) = r < \min(n,m)`. The pseudo inverse $`\mathbf{A}^+` can be constructed from the singular value decomposition $`\mathbf{A} = \mathbf{U}\mathbf{D}\mathbf{V}^T`, by

  $$`\mathbf{A}^+ = \mathbf{V}_r\mathbf{D}_r^{-1}\mathbf{U}_r^T \tag{223}`
-/
theorem eq_223 : (sorry : Prop) :=
  sorry

/--
> where $`\mathbf{U}_r, \mathbf{D}_r`, and $`\mathbf{V}_r` are the matrices with the degenerated rows and columns deleted. A different way is this: There do always exist two matrices $`\mathbf{C}` $`n\times r` and $`\mathbf{D}` $`r\times m` of rank $`r`, such that $`\mathbf{A} = \mathbf{C}\mathbf{D}`. Using these matrices it holds that

  $$`\mathbf{A}^+ = \mathbf{D}^T(\mathbf{D}\mathbf{D}^T)^{-1}(\mathbf{C}^T\mathbf{C})^{-1}\mathbf{C}^T \tag{224}`
-/
theorem eq_224 : (sorry : Prop) :=
  sorry

/-!
> See \[3\].
-/

end MatrixCookbook
