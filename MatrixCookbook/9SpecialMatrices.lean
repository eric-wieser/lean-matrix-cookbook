module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Matrix.PEquiv
public import Mathlib.Data.Matrix.Reflection
public import Mathlib.Analysis.Matrix.Hermitian
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Symmetric
public import Mathlib.LinearAlgebra.Vandermonde
public import Mathlib.Algebra.Order.Star.Real
public import MatrixCookbook.ForMathlib.Data.Matrix
public import MatrixCookbook.ForMathlib.Data.Matrix.Toeplitz
public import MatrixCookbook.ForMathlib.Data.Matrix.RowCol

set_option doc.verso true

/-!
# Special Matrices

## Block matrices

> Let $`\mathbf{A}_{ij}` denote the $`ij`th block of $`\mathbf{A}`.

### Multiplication

> Assuming the dimensions of the blocks matches we have

  $$`\left[\begin{array}{c|c} \mathbf{A}_{11} & \mathbf{A}_{12} \\ \hline \mathbf{A}_{21} & \mathbf{A}_{22} \end{array}\right]\left[\begin{array}{c|c} \mathbf{B}_{11} & \mathbf{B}_{12} \\ \hline \mathbf{B}_{21} & \mathbf{B}_{22} \end{array}\right] = \left[\begin{array}{c|c} \mathbf{A}_{11}\mathbf{B}_{11}+\mathbf{A}_{12}\mathbf{B}_{21} & \mathbf{A}_{11}\mathbf{B}_{12}+\mathbf{A}_{12}\mathbf{B}_{22} \\ \hline \mathbf{A}_{21}\mathbf{B}_{11}+\mathbf{A}_{22}\mathbf{B}_{21} & \mathbf{A}_{21}\mathbf{B}_{12}+\mathbf{A}_{22}\mathbf{B}_{22} \end{array}\right]`

### The Determinant
-/

@[expose] public section

variable {R : Type _} {l m n p q r : Type _}

variable [Fintype l] [Fintype m] [Fintype n] [Fintype p] [Fintype q] [Fintype r]

variable [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]
  [DecidableEq r]

variable [Field R]

open Matrix

open scoped BigOperators

open scoped Matrix

namespace MatrixCookbook

/--
> The determinant can be expressed as by the use of

  $$`\mathbf{C}_1 = \mathbf{A}_{11}-\mathbf{A}_{12}\mathbf{A}_{22}^{-1}\mathbf{A}_{21} \tag{397}`
-/
theorem eq_397 (A₁₁ : Matrix m m R) (A₁₂ : Matrix m n R) (A₂₁ : Matrix n m R) (A₂₂ : Matrix n n R)
    [Invertible A₂₂] : (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).det = A₂₂.det * (A₁₁ - A₁₂ * ⅟ A₂₂ * A₂₁).det :=
  det_fromBlocks₂₂ _ _ _ _

/--
> $$`\mathbf{C}_2 = \mathbf{A}_{22}-\mathbf{A}_{21}\mathbf{A}_{11}^{-1}\mathbf{A}_{12} \tag{398}`
-/
theorem eq_398 (A₁₁ : Matrix m m R) (A₁₂ : Matrix m n R) (A₂₁ : Matrix n m R) (A₂₂ : Matrix n n R)
    [Invertible A₁₁] : (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂).det = A₁₁.det * (A₂₂ - A₂₁ * ⅟ A₁₁ * A₁₂).det :=
  det_fromBlocks₁₁ _ _ _ _

/-!
> as

  $$`\det\left(\left[\begin{array}{c|c} \mathbf{A}_{11} & \mathbf{A}_{12} \\ \hline \mathbf{A}_{21} & \mathbf{A}_{22} \end{array}\right]\right) = \det(\mathbf{A}_{22})\cdot\det(\mathbf{C}_1) = \det(\mathbf{A}_{11})\cdot\det(\mathbf{C}_2)`

### The Inverse
-/

/--
> The inverse can be expressed as by the use of

  $$`\mathbf{C}_1 = \mathbf{A}_{11}-\mathbf{A}_{12}\mathbf{A}_{22}^{-1}\mathbf{A}_{21} \tag{399}`

Eq 399 is the definition of {lit}`C₁`, this is the equation below it without {lit}`C₂` at all.
-/
theorem eq_399 (A₁₁ : Matrix m m R) (A₁₂ : Matrix m n R) (A₂₁ : Matrix n m R) (A₂₂ : Matrix n n R)
    [Invertible A₂₂] [Invertible (A₁₁ - A₁₂ * ⅟ A₂₂ * A₂₁)] :
    (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)⁻¹ =
      let C₁ := A₁₁ - A₁₂ * ⅟ A₂₂ * A₂₁
      let i : Invertible C₁ := ‹_›
      fromBlocks
        (⅟ C₁) (-(⅟ C₁ * A₁₂ * ⅟ A₂₂))
        (-(⅟ A₂₂ * A₂₁ * ⅟ C₁)) (⅟ A₂₂ + ⅟ A₂₂ * A₂₁ * ⅟ C₁ * A₁₂ * ⅟ A₂₂) := by
  let := fromBlocks₂₂Invertible A₁₁ A₁₂ A₂₁ A₂₂
  convert invOf_fromBlocks₂₂_eq A₁₁ A₁₂ A₂₁ A₂₂
  rw [invOf_eq_nonsing_inv]

/--
> $$`\mathbf{C}_2 = \mathbf{A}_{22}-\mathbf{A}_{21}\mathbf{A}_{11}^{-1}\mathbf{A}_{12} \tag{400}`

Eq 400 is the definition of {lit}`C₂`,  this is the equation below it without {lit}`C₁` at all.
-/
theorem eq_400 (A₁₁ : Matrix m m R) (A₁₂ : Matrix m n R) (A₂₁ : Matrix n m R) (A₂₂ : Matrix n n R)
    [Invertible A₁₁] [Invertible (A₂₂ - A₂₁ * ⅟ A₁₁ * A₁₂)] :
    (fromBlocks A₁₁ A₁₂ A₂₁ A₂₂)⁻¹ =
      let C₂ := A₂₂ - A₂₁ * ⅟ A₁₁ * A₁₂
      let i : Invertible C₂ := ‹_›
      fromBlocks
        (⅟ A₁₁ + ⅟ A₁₁ * A₁₂ * ⅟ C₂ * A₂₁ * ⅟ A₁₁) (-(⅟ A₁₁ * A₁₂ * ⅟ C₂))
        (-(⅟ C₂ * A₂₁ * ⅟ A₁₁)) (⅟ C₂) := by
  let := fromBlocks₁₁Invertible A₁₁ A₁₂ A₂₁ A₂₂
  convert invOf_fromBlocks₁₁_eq A₁₁ A₁₂ A₂₁ A₂₂
  rw [invOf_eq_nonsing_inv]

/-!
> as

  $$`\begin{aligned} & \left[\begin{array}{c|c} \mathbf{A}_{11} & \mathbf{A}_{12} \\ \hline \mathbf{A}_{21} & \mathbf{A}_{22} \end{array}\right]^{-1} = \left[\begin{array}{c|c} \mathbf{C}_1^{-1} & -\mathbf{A}_{11}^{-1}\mathbf{A}_{12}\mathbf{C}_2^{-1} \\ \hline -\mathbf{C}_2^{-1}\mathbf{A}_{21}\mathbf{A}_{11}^{-1} & \mathbf{C}_2^{-1} \end{array}\right] \\ = {} & \left[\begin{array}{c|c} \mathbf{A}_{11}^{-1}+\mathbf{A}_{11}^{-1}\mathbf{A}_{12}\mathbf{C}_2^{-1}\mathbf{A}_{21}\mathbf{A}_{11}^{-1} & -\mathbf{C}_1^{-1}\mathbf{A}_{12}\mathbf{A}_{22}^{-1} \\ \hline -\mathbf{A}_{22}^{-1}\mathbf{A}_{21}\mathbf{C}_1^{-1} & \mathbf{A}_{22}^{-1}+\mathbf{A}_{22}^{-1}\mathbf{A}_{21}\mathbf{C}_1^{-1}\mathbf{A}_{12}\mathbf{A}_{22}^{-1} \end{array}\right] \end{aligned}`

### Block diagonal
-/

/--
> For block diagonal matrices we have

  $$`\left[\begin{array}{c|c} \mathbf{A}_{11} & \mathbf{0} \\ \hline \mathbf{0} & \mathbf{A}_{22} \end{array}\right]^{-1} = \left[\begin{array}{c|c} (\mathbf{A}_{11})^{-1} & \mathbf{0} \\ \hline \mathbf{0} & (\mathbf{A}_{22})^{-1} \end{array}\right] \tag{401}`
-/
theorem eq_401 (A₁₁ : Matrix m m R) (A₂₂ : Matrix n n R) (h : IsUnit A₁₁ ↔ IsUnit A₂₂) :
    (fromBlocks A₁₁ 0 0 A₂₂)⁻¹ = fromBlocks A₁₁⁻¹ 0 0 A₂₂⁻¹ :=
  (inv_fromBlocks_zero₁₂_of_isUnit_iff _ _ _ h).trans <| by simp

/--
> $$`\det\left(\left[\begin{array}{c|c} \mathbf{A}_{11} & \mathbf{0} \\ \hline \mathbf{0} & \mathbf{A}_{22} \end{array}\right]\right) = \det(\mathbf{A}_{11})\cdot\det(\mathbf{A}_{22}) \tag{402}`
-/
theorem eq_402 (A₁₁ : Matrix m m R) (A₂₂ : Matrix n n R) :
    det (fromBlocks A₁₁ 0 0 A₂₂) = det A₁₁ * det A₂₂ :=
  det_fromBlocks_zero₁₂ _ _ _

/-!
### Schur complement

> Regard the matrix

  $$`\left[\begin{array}{c|c} \mathbf{A}_{11} & \mathbf{A}_{12} \\ \hline \mathbf{A}_{21} & \mathbf{A}_{22} \end{array}\right]`

  The Schur complement of block $`\mathbf{A}_{11}` of the matrix above is the matrix (denoted $`\mathbf{C}_2` in the text above)

  $$`\mathbf{A}_{22}-\mathbf{A}_{21}\mathbf{A}_{11}^{-1}\mathbf{A}_{12}`

  The Schur complement of block $`\mathbf{A}_{22}` of the matrix above is the matrix (denoted $`\mathbf{C}_1` in the text above)

  $$`\mathbf{A}_{11}-\mathbf{A}_{12}\mathbf{A}_{22}^{-1}\mathbf{A}_{21}`

  Using the Schur complement, one can rewrite the inverse of a block matrix

  $$`\begin{aligned} & \left[\begin{array}{c|c} \mathbf{A}_{11} & \mathbf{A}_{12} \\ \hline \mathbf{A}_{21} & \mathbf{A}_{22} \end{array}\right]^{-1} \\ = {} & \left[\begin{array}{c|c} \mathbf{I} & \mathbf{0} \\ \hline -\mathbf{A}_{22}^{-1}\mathbf{A}_{21} & \mathbf{I} \end{array}\right]\left[\begin{array}{c|c} (\mathbf{A}_{11}-\mathbf{A}_{12}\mathbf{A}_{22}^{-1}\mathbf{A}_{21})^{-1} & \mathbf{0} \\ \hline \mathbf{0} & \mathbf{A}_{22}^{-1} \end{array}\right]\left[\begin{array}{c|c} \mathbf{I} & -\mathbf{A}_{12}\mathbf{A}_{22}^{-1} \\ \hline \mathbf{0} & \mathbf{I} \end{array}\right] \end{aligned}`

  The Schur complement is useful when solving linear systems of the form

  $$`\left[\begin{array}{c|c} \mathbf{A}_{11} & \mathbf{A}_{12} \\ \hline \mathbf{A}_{21} & \mathbf{A}_{22} \end{array}\right]\left[\begin{array}{c} \mathbf{x}_1 \\ \hline \mathbf{x}_2 \end{array}\right] = \left[\begin{array}{c} \mathbf{b}_1 \\ \hline \mathbf{b}_2 \end{array}\right]`

  which has the following equation for $`\mathbf{x}_1`

  $$`(\mathbf{A}_{11}-\mathbf{A}_{12}\mathbf{A}_{22}^{-1}\mathbf{A}_{21})\mathbf{x}_1 = \mathbf{b}_1-\mathbf{A}_{12}\mathbf{A}_{22}^{-1}\mathbf{b}_2`

  When the appropriate inverses exists, this can be solved for $`\mathbf{x}_1` which can then be inserted in the equation for $`\mathbf{x}_2` to solve for $`\mathbf{x}_2`.

## Discrete Fourier Transform Matrix, The
-/

/--
> The DFT matrix is an $`N\times N` symmetric matrix $`\mathbf{W}_N`, where the $`k,n`th element is given by

  $$`W_N^{kn} = e^{\frac{-j2\pi kn}{N}} \tag{403}`
-/
theorem eq_403 : (sorry : Prop) :=
  sorry

/--
> Thus the discrete Fourier transform (DFT) can be expressed as

  $$`X(k) = \sum_{n=0}^{N-1}x(n)W_N^{kn}. \tag{404}`
-/
theorem eq_404 : (sorry : Prop) :=
  sorry

/--
> Likewise the inverse discrete Fourier transform (IDFT) can be expressed as

  $$`x(n) = \frac{1}{N}\sum_{k=0}^{N-1}X(k)W_N^{-kn}. \tag{405}`
-/
theorem eq_405 : (sorry : Prop) :=
  sorry

/--
> The DFT of the vector $`\mathbf{x} = [x(0), x(1), \cdots, x(N-1)]^T` can be written in matrix form as

  $$`\mathbf{X} = \mathbf{W}_N\mathbf{x}, \tag{406}`
-/
theorem eq_406 : (sorry : Prop) :=
  sorry

/--
> where $`\mathbf{X} = [X(0), X(1), \cdots, x(N-1)]^T`. The IDFT is similarly given as

  $$`\mathbf{x} = \mathbf{W}_N^{-1}\mathbf{X}. \tag{407}`
-/
theorem eq_407 : (sorry : Prop) :=
  sorry

/--
> Some properties of $`\mathbf{W}_N` exist:

  $$`\mathbf{W}_N^{-1} = \frac{1}{N}\mathbf{W}_N^* \tag{408}`
-/
theorem eq_408 : (sorry : Prop) :=
  sorry

/--
> $$`\mathbf{W}_N\mathbf{W}_N^* = N\mathbf{I} \tag{409}`
-/
theorem eq_409 : (sorry : Prop) :=
  sorry

/--
> $$`\mathbf{W}_N^* = \mathbf{W}_N^H \tag{410}`
-/
theorem eq_410 : (sorry : Prop) :=
  sorry

/--
> If $`W_N = e^{\frac{-j2\pi}{N}}`, then \[23\]

  $$`W_N^{m+N/2} = -W_N^m \tag{411}`
-/
theorem eq_411 : (sorry : Prop) :=
  sorry

/-!
> Notice, the DFT matrix is a Vandermonde Matrix.
-/

/--
> The following important relation between the circulant matrix and the discrete Fourier transform (DFT) exists

  $$`\mathbf{T}_C = \mathbf{W}_N^{-1}(\mathbf{I}\circ(\mathbf{W}_N\mathbf{t}))\mathbf{W}_N, \tag{412}`
-/
theorem eq_412 : (sorry : Prop) :=
  sorry

/-!
> where $`\mathbf{t} = [t_0, t_1, \cdots, t_{n-1}]^T` is the first row of $`\mathbf{T}_C`.

## Hermitian Matrices and skew-Hermitian

> A matrix $`\mathbf{A}\in\mathbb{C}^{m\times n}` is called _Hermitian_ if

  $$`\mathbf{A}^H = \mathbf{A}`
-/

/--
> For real valued matrices, Hermitian and symmetric matrices are equivalent.

  $$`\mathbf{A}\text{ is Hermitian} \quad\Leftrightarrow\quad \mathbf{x}^H\mathbf{A}\mathbf{x}\in\mathbb{R}, \quad \forall\mathbf{x}\in\mathbb{C}^{n\times 1} \tag{413}`
-/
theorem eq_413 (A : Matrix m m ℂ) :
    A.IsHermitian ↔ ∀ x : m → ℂ, IsSelfAdjoint (star x ⬝ᵥ A.mulVec x) := by
  rw [← isSymmetric_toEuclideanLin_iff, LinearMap.isSymmetric_iff_inner_map_self_real,
    ← (WithLp.equiv 2 (m → ℂ)).symm.forall_congr_right]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm _ (star _),
    star_dotProduct (A *ᵥ _), isSelfAdjoint_iff, eq_comm]

/--
> $$`\mathbf{A}\text{ is Hermitian} \quad\Leftrightarrow\quad \operatorname{eig}(\mathbf{A})\in\mathbb{R} \tag{414}`
-/
theorem eq_414 (A : Matrix m m ℂ) : A.IsHermitian ↔ sorry :=
  sorry

/-!
> Note that

  $$`\mathbf{A} = \mathbf{B}+i\mathbf{C}`

  where $`\mathbf{B}, \mathbf{C}` are hermitian, then

  $$`\mathbf{B} = \frac{\mathbf{A}+\mathbf{A}^H}{2}, \qquad \mathbf{C} = \frac{\mathbf{A}-\mathbf{A}^H}{2i}`

### Skew-Hermitian

> A matrix $`\mathbf{A}` is called _skew-hermitian_ if

  $$`\mathbf{A} = -\mathbf{A}^H`
-/

/--
> For real valued matrices, skew-Hermitian and skew-symmetric matrices are equivalent.

  $$`\mathbf{A}\text{ Hermitian} \quad\Leftrightarrow\quad i\mathbf{A}\text{ is skew-hermitian} \tag{415}`
-/
theorem eq_415 (A : Matrix m m ℂ) : A.IsHermitian ↔ Complex.I • A ∈ skewAdjoint (Matrix m m ℂ) :=
  ⟨fun h => h.isSelfAdjoint.I_smul_mem_skewAdjoint (K := ℂ),
   fun h => IsSelfAdjoint.isHermitian <| by
     simpa [smul_smul] using (IsSelfAdjoint.I_smul_of_mem_skewAdjoint (K := ℂ) h).neg⟩

/--
> $$`\mathbf{A}\text{ skew-Hermitian} \quad\Leftrightarrow\quad \mathbf{x}^H\mathbf{A}\mathbf{y} = -\mathbf{x}^H\mathbf{A}^H\mathbf{y}, \quad \forall\mathbf{x},\mathbf{y} \tag{416}`
-/
theorem eq_416 (A : Matrix m m ℂ) :
    A ∈ skewAdjoint (Matrix m m ℂ) ↔ ∀ x y, star x ⬝ᵥ A.mulVec y = -star x ⬝ᵥ Aᴴ.mulVec y := by
  rw [skewAdjoint.mem_iff, star_eq_conjTranspose, ← neg_eq_iff_eq_neg, eq_comm, ext_iff_mulVec,
    forall_comm]
  refine forall_congr' fun y => ?_
  rw [star_involutive.surjective.forall, ← dotProduct_eq_iff]
  simp [dotProduct_comm _ (A *ᵥ y), dotProduct_comm _ (Aᴴ *ᵥ y), neg_mulVec]

/--
> $$`\mathbf{A}\text{ skew-Hermitian} \quad\Rightarrow\quad \operatorname{eig}(\mathbf{A}) = i\lambda, \quad \lambda\in\mathbb{R} \tag{417}`
-/
theorem eq_417 (A : Matrix m m ℂ) : A.IsHermitian → (sorry : Prop) :=
  sorry

section

variable (A : Matrix m m R) (B : Matrix m m R)

/-!
## Idempotent Matrices

> A matrix $`\mathbf{A}` is idempotent if

  $$`\mathbf{A}\mathbf{A} = \mathbf{A}`
-/

/--
> Idempotent matrices $`\mathbf{A}` and $`\mathbf{B}`, have the following properties

  $$`\mathbf{A}^n = \mathbf{A}, \qquad \text{for} n = 1, 2, 3, ... \tag{418}`
-/
theorem eq_418 (hA : IsIdempotentElem A) (n : ℕ) (hn : n ≠ 0) : A ^ n = A := by
  obtain _ | n := n
  · cases hn rfl
  · exact hA.pow_succ_eq n

/--
> $$`\mathbf{I}-\mathbf{A} \quad \text{is idempotent} \tag{419}`
-/
theorem eq_419 (hA : IsIdempotentElem A) : IsIdempotentElem (1 - A) :=
  hA.one_sub

/--
> $$`\mathbf{A}^H \quad \text{is idempotent} \tag{420}`
-/
theorem eq_420 [StarRing R] (hA : IsIdempotentElem A) : IsIdempotentElem Aᴴ :=
  hA.star

/--
> $$`\mathbf{I}-\mathbf{A}^H \quad \text{is idempotent} \tag{421}`
-/
theorem eq_421 [StarRing R] (hA : IsIdempotentElem A) : IsIdempotentElem (1 - Aᴴ) :=
  hA.star.one_sub

/--
> $$`\text{If } \mathbf{A}\mathbf{B} = \mathbf{B}\mathbf{A} \quad\Rightarrow\quad \mathbf{A}\mathbf{B} \quad \text{is idempotent} \tag{422}`
-/
theorem eq_422 (hA : IsIdempotentElem A) (hB : IsIdempotentElem B) (h : Commute A B) :
    IsIdempotentElem (A * B) :=
  hA.mul_of_commute h hB

/--
> $$`\operatorname{rank}(\mathbf{A}) = \operatorname{Tr}(\mathbf{A}) \tag{423}`
-/
theorem eq_423 (hA : IsIdempotentElem A) : sorry = trace A :=
  sorry

/--
> $$`\mathbf{A}(\mathbf{I}-\mathbf{A}) = \mathbf{0} \tag{424}`
-/
theorem eq_424 (hA : IsIdempotentElem A) : A * (1 - A) = 0 := by
  simp [mul_sub, hA.eq]

/--
> $$`(\mathbf{I}-\mathbf{A})\mathbf{A} = \mathbf{0} \tag{425}`
-/
theorem eq_425 (hA : IsIdempotentElem A) : (1 - A) * A = 0 := by
  simp [sub_mul, hA.eq]

/--
> $$`\mathbf{A}^+ = \mathbf{A} \tag{426}`
-/
theorem eq_426 : (sorry : Prop) :=
  sorry

/--
> $$`f(s\mathbf{I}+t\mathbf{A}) = (\mathbf{I}-\mathbf{A})f(s)+\mathbf{A}f(s+t) \tag{427}`
-/
theorem eq_427 : (sorry : Prop) :=
  sorry

end

/-!
> Note that $`\mathbf{A}-\mathbf{I}` is not necessarily idempotent.

### Nilpotent

> A matrix $`\mathbf{A}` is nilpotent if

  $$`\mathbf{A}^2 = \mathbf{0}`
-/

/--
> A nilpotent matrix has the following property:

  $$`f(s\mathbf{I}+t\mathbf{A}) = \mathbf{I}f(s)+t\mathbf{A}f'(s) \tag{428}`
-/
theorem eq_428 : (sorry : Prop) :=
  sorry

/-!
### Unipotent

> A matrix $`\mathbf{A}` is unipotent if

  $$`\mathbf{A}\mathbf{A} = \mathbf{I}`
-/

/--
> A unipotent matrix has the following property:

  $$`f(s\mathbf{I}+t\mathbf{A}) = [(\mathbf{I}+\mathbf{A})f(s+t)+(\mathbf{I}-\mathbf{A})f(s-t)]/2 \tag{429}`
-/
theorem eq_429 : (sorry : Prop) :=
  sorry

/-!
## Orthogonal matrices

> If a square matrix $`\mathbf{Q}` is orthogonal, if and only if,

  $$`\mathbf{Q}^T\mathbf{Q} = \mathbf{Q}\mathbf{Q}^T = \mathbf{I}`

  and then $`\mathbf{Q}` has the following properties

  • Its eigenvalues are placed on the unit circle.

  • Its eigenvectors are unitary, i.e. have length one.

  • The inverse of an orthogonal matrix is orthogonal too.

  Basic properties for the orthogonal matrix $`\mathbf{Q}`

  $$`\begin{aligned} \mathbf{Q}^{-1} &= \mathbf{Q}^T \\ \mathbf{Q}^{-T} &= \mathbf{Q} \\ \mathbf{Q}\mathbf{Q}^T &= \mathbf{I} \\ \mathbf{Q}^T\mathbf{Q} &= \mathbf{I} \\ \det(\mathbf{Q}) &= \pm 1 \end{aligned}`

### Ortho-Sym
-/

/--
> A matrix $`\mathbf{Q}_+` which simultaneously is orthogonal and symmetric is called an ortho-sym matrix \[20\]. Hereby

  $$`\mathbf{Q}_+^T\mathbf{Q}_+ = \mathbf{I} \tag{430}`
-/
theorem eq_430 : (sorry : Prop) :=
  sorry

/--
> $$`\mathbf{Q}_+ = \mathbf{Q}_+^T \tag{431}`
-/
theorem eq_431 : (sorry : Prop) :=
  sorry

/--
> The powers of an ortho-sym matrix are given by the following rule

  $$`\mathbf{Q}_+^k = \frac{1+(-1)^k}{2}\mathbf{I}+\frac{1+(-1)^{k+1}}{2}\mathbf{Q}_+ \tag{432}`
-/
theorem eq_432 : (sorry : Prop) :=
  sorry

/--
> $$`= \frac{1+\cos(k\pi)}{2}\mathbf{I}+\frac{1-\cos(k\pi)}{2}\mathbf{Q}_+ \tag{433}`
-/
theorem eq_433 : (sorry : Prop) :=
  sorry

/-!
### Ortho-Skew
-/

/--
> A matrix which simultaneously is orthogonal and antisymmetric is called an ortho-skew matrix \[20\]. Hereby

  $$`\mathbf{Q}_-^H\mathbf{Q}_- = \mathbf{I} \tag{434}`
-/
theorem eq_434 : (sorry : Prop) :=
  sorry

/--
> $$`\mathbf{Q}_- = -\mathbf{Q}_-^H \tag{435}`
-/
theorem eq_435 : (sorry : Prop) :=
  sorry

/--
> The powers of an ortho-skew matrix are given by the following rule

  $$`\mathbf{Q}_-^k = \frac{i^k+(-i)^k}{2}\mathbf{I}-i\frac{i^k-(-i)^k}{2}\mathbf{Q}_- \tag{436}`
-/
theorem eq_436 : (sorry : Prop) :=
  sorry

/--
> $$`= \cos(k\frac{\pi}{2})\mathbf{I}+\sin(k\frac{\pi}{2})\mathbf{Q}_- \tag{437}`
-/
theorem eq_437 : (sorry : Prop) :=
  sorry

/-!
### Decomposition
-/

/--
> A square matrix $`\mathbf{A}` can always be written as a sum of a symmetric $`\mathbf{A}_+` and an antisymmetric matrix $`\mathbf{A}_-`

  $$`\mathbf{A} = \mathbf{A}_+ + \mathbf{A}_- \tag{438}`
-/
theorem eq_438 : (sorry : Prop) :=
  sorry

/-!
## Positive Definite and Semi-definite Matrices

### Definitions
-/

/--
> A matrix $`\mathbf{A}` is positive definite if and only if

  $$`\mathbf{x}^T\mathbf{A}\mathbf{x} > \mathbf{0}, \quad \forall\mathbf{x}\neq\mathbf{0} \tag{439}`

Note: the source omits the symmetry condition, without which this is false.
-/
theorem eq_439 (A : Matrix n n ℝ) : A.PosDef ↔ A.IsSymm ∧ ∀ x ≠ 0, x ⬝ᵥ A.mulVec x > 0 := by
  simpa [IsHermitian, IsSymm] using posDef_iff_dotProduct_mulVec (M := A)

/--
> A matrix $`\mathbf{A}` is positive semi-definite if and only if

  $$`\mathbf{x}^T\mathbf{A}\mathbf{x} \geq \mathbf{0}, \quad \forall\mathbf{x} \tag{440}`

Note: the source omits the symmetry condition, without which this is false.
-/
theorem eq_440 (A : Matrix n n ℝ) : A.PosSemidef ↔ A.IsSymm ∧ ∀ x, x ⬝ᵥ A.mulVec x ≥ 0 := by
  simpa [IsHermitian, IsSymm] using posSemidef_iff_dotProduct_mulVec (M := A)

/-!
> Note that if $`\mathbf{A}` is positive definite, then $`\mathbf{A}` is also positive semi-definite.

### Eigenvalues
-/

/--
> The following holds with respect to the eigenvalues:

  $$`\begin{array}{rcl} \mathbf{A}\text{ pos. def.} & \Leftrightarrow & \operatorname{eig}(\frac{\mathbf{A}+\mathbf{A}^H}{2}) > 0 \\ \mathbf{A}\text{ pos. semi-def.} & \Leftrightarrow & \operatorname{eig}(\frac{\mathbf{A}+\mathbf{A}^H}{2}) \geq 0 \end{array} \tag{441}`
-/
theorem eq_441 : (sorry : Prop) :=
  sorry

/-!
### Trace
-/

/--
> The following holds with respect to the trace:

  $$`\begin{array}{rcl} \mathbf{A}\text{ pos. def.} & \Rightarrow & \operatorname{Tr}(\mathbf{A}) > 0 \\ \mathbf{A}\text{ pos. semi-def.} & \Rightarrow & \operatorname{Tr}(\mathbf{A}) \geq 0 \end{array} \tag{442}`
-/
theorem eq_442 : (sorry : Prop) :=
  sorry

/-!
### Inverse

> If $`\mathbf{A}` is positive definite, then $`\mathbf{A}` is invertible and $`\mathbf{A}^{-1}` is also positive definite.

### Diagonal

> If $`\mathbf{A}` is positive definite, then $`A_{ii} > 0, \forall i`

### Decomposition I

> The matrix $`\mathbf{A}` is positive semi-definite of rank $`r` $`\Leftrightarrow` there exists a matrix $`\mathbf{B}` of rank $`r` such that $`\mathbf{A} = \mathbf{B}\mathbf{B}^T`

  The matrix $`\mathbf{A}` is positive definite $`\Leftrightarrow` there exists an invertible matrix $`\mathbf{B}` such that $`\mathbf{A} = \mathbf{B}\mathbf{B}^T`

### Decomposition II

> Assume $`\mathbf{A}` is an $`n\times n` positive semi-definite, then there exists an $`n\times r` matrix $`\mathbf{B}` of rank $`r` such that $`\mathbf{B}^T\mathbf{A}\mathbf{B} = \mathbf{I}`.

### Equation with zeros

> Assume $`\mathbf{A}` is positive semi-definite, then $`\mathbf{X}^T\mathbf{A}\mathbf{X} = \mathbf{0} \quad\Rightarrow\quad \mathbf{A}\mathbf{X} = \mathbf{0}`

### Rank of product

> Assume $`\mathbf{A}` is positive definite, then $`\operatorname{rank}(\mathbf{B}\mathbf{A}\mathbf{B}^T) = \operatorname{rank}(\mathbf{B})`

### Positive definite property

> If $`\mathbf{A}` is $`n\times n` positive definite and $`\mathbf{B}` is $`r\times n` of rank $`r`, then $`\mathbf{B}\mathbf{A}\mathbf{B}^T` is positive definite.

### Outer Product

> If $`\mathbf{X}` is $`n\times r`, where $`n\leq r` and $`\operatorname{rank}(\mathbf{X}) = n`, then $`\mathbf{X}\mathbf{X}^T` is positive definite.

### Small pertubations

> If $`\mathbf{A}` is positive definite and $`\mathbf{B}` is symmetric, then $`\mathbf{A}-t\mathbf{B}` is positive definite for sufficiently small $`t`.

### Hadamard inequality

> If $`\mathbf{A}` is a positive definite or semi-definite matrix, then

  $$`\det(\mathbf{A}) \leq \prod_i A_{ii}`

  See \[15, pp.477\]

### Hadamard product relation

> Assume that $`\mathbf{P} = \mathbf{A}\mathbf{A}^T` and $`\mathbf{Q} = \mathbf{B}\mathbf{B}^T` are semi positive definite matrices, it then holds that

  $$`\mathbf{P}\circ\mathbf{Q} = \mathbf{R}\mathbf{R}^T`

  where the columns of $`\mathbf{R}` are constructed as follows: $`\mathbf{r}_{i+(j-1)N_A} = \mathbf{a}_i\circ\mathbf{b}_j`, for $`i = 1, 2, ..., N_A` and $`j = 1, 2, ..., N_B`. The result is unpublished, but reported by Pavel Sakov and Craig Bishop.

## Singleentry Matrix, The

### Definition
-/

/--
> The single-entry matrix $`\mathbf{J}^{ij}\in\mathbb{R}^{n\times n}` is defined as the matrix which is zero everywhere except in the entry $`(i,j)` in which it is 1. In a $`4\times 4` example one might have

  $$`\mathbf{J}^{23} = \begin{bmatrix} 0 & 0 & 0 & 0 \\ 0 & 0 & 1 & 0 \\ 0 & 0 & 0 & 0 \\ 0 & 0 & 0 & 0 \end{bmatrix} \tag{443}`
-/
-- note this is 0-indexed not 1-indexed
theorem eq_443 :
    single (1 : Fin 4) (2 : Fin 4) 1 =
      !![0, 0, 0, 0;
         0, 0, 1, 0;
         0, 0, 0, 0;
         0, 0, 0, 0] := by
  decide

/-!
> The single-entry matrix is very useful when working with derivatives of expressions involving matrices.

### Swap and Zeros
-/

/--
> Assume $`\mathbf{A}` to be $`n\times m` and $`\mathbf{J}^{ij}` to be $`m\times p`

  $$`\mathbf{A}\mathbf{J}^{ij} = \begin{bmatrix} \mathbf{0} & \mathbf{0} & \ldots & \mathbf{A}_i & \ldots & \mathbf{0} \end{bmatrix} \tag{444}`
-/
theorem eq_444 (A : Matrix n m R) (i : m) (j : p) :
    A * single i j (1 : R) = updateCol 0 j (A.col i) := by
  rw [mul_single_eq_updateCol_zero, MulOpposite.op_one, one_smul]

/--
> i.e. an $`n\times p` matrix of zeros with the i.th column of $`\mathbf{A}` in place of the j.th column. Assume $`\mathbf{A}` to be $`n\times m` and $`\mathbf{J}^{ij}` to be $`p\times n`

  $$`\mathbf{J}^{ij}\mathbf{A} = \begin{bmatrix} \mathbf{0} \\ \vdots \\ \mathbf{0} \\ \mathbf{A}_j \\ \mathbf{0} \\ \vdots \\ \mathbf{0} \end{bmatrix} \tag{445}`
-/
theorem eq_445 (i : p) (j : n) (A : Matrix n m R) :
    single i j (1 : R) * A = updateRow 0 i (A.row j) := by
  rw [single_mul_eq_updateRow_zero, one_smul]

/-!
> i.e. an $`p\times m` matrix of zeros with the j.th row of $`\mathbf{A}` in the placed of the i.th row.

### Rewriting product of elements
-/

/--
> $$`A_{ki}B_{jl} = (\mathbf{A}\mathbf{e}_i\mathbf{e}_j^T\mathbf{B})_{kl} = (\mathbf{A}\mathbf{J}^{ij}\mathbf{B})_{kl} \tag{446}`
-/
theorem eq_446 (A : Matrix l m R) (B : Matrix n p R) (k i j l) :
    A k i * B j l = (A * single i j (1 : R) * B) k l := by
  rw [eq_444, Matrix.mul_apply]
  rw [Fintype.sum_eq_single j, updateCol_self, col_apply]
  · simp +contextual

/--
> $$`A_{ik}B_{lj} = (\mathbf{A}^T\mathbf{e}_i\mathbf{e}_j^T\mathbf{B}^T)_{kl} = (\mathbf{A}^T\mathbf{J}^{ij}\mathbf{B}^T)_{kl} \tag{447}`
-/
theorem eq_447 (A : Matrix l m R) (B : Matrix n p R) (k i j l) :
    A i k * B l j = (Aᵀ * single i j (1 : R) * Bᵀ) k l := by
  rw [←eq_446]; rfl

/--
> $$`A_{ik}B_{jl} = (\mathbf{A}^T\mathbf{e}_i\mathbf{e}_j^T\mathbf{B})_{kl} = (\mathbf{A}^T\mathbf{J}^{ij}\mathbf{B})_{kl} \tag{448}`
-/
theorem eq_448 (A : Matrix l m R) (B : Matrix n p R) (k i j l) :
    A i k * B j l = (Aᵀ * single i j (1 : R) * B) k l := by
  rw [←eq_446]; rfl

/--
> $$`A_{ki}B_{lj} = (\mathbf{A}\mathbf{e}_i\mathbf{e}_j^T\mathbf{B}^T)_{kl} = (\mathbf{A}\mathbf{J}^{ij}\mathbf{B}^T)_{kl} \tag{449}`
-/
theorem eq_449 (A : Matrix l m R) (B : Matrix n p R) (k i j l) :
    A k i * B l j = (A * single i j (1 : R) * Bᵀ) k l := by
  rw [←eq_446]; rfl

/-!
### Properties of the Singleentry Matrix

> If $`i = j`

  $$`\mathbf{J}^{ij}\mathbf{J}^{ij} = \mathbf{J}^{ij} \qquad (\mathbf{J}^{ij})^T(\mathbf{J}^{ij})^T = \mathbf{J}^{ij}`

  $$`\mathbf{J}^{ij}(\mathbf{J}^{ij})^T = \mathbf{J}^{ij} \qquad (\mathbf{J}^{ij})^T\mathbf{J}^{ij} = \mathbf{J}^{ij}`

  If $`i\neq j`

  $$`\mathbf{J}^{ij}\mathbf{J}^{ij} = \mathbf{0} \qquad (\mathbf{J}^{ij})^T(\mathbf{J}^{ij})^T = \mathbf{0}`

  $$`\mathbf{J}^{ij}(\mathbf{J}^{ij})^T = \mathbf{J}^{ii} \qquad (\mathbf{J}^{ij})^T\mathbf{J}^{ij} = \mathbf{J}^{jj}`

### The Singleentry Matrix in Scalar Expressions
-/

/--
> Assume $`\mathbf{A}` is $`n\times m` and $`\mathbf{J}` is $`m\times n`, then

  $$`\operatorname{Tr}(\mathbf{A}\mathbf{J}^{ij}) = \operatorname{Tr}(\mathbf{J}^{ij}\mathbf{A}) = (\mathbf{A}^T)_{ij} \tag{450}`
-/
theorem eq_450 (A : Matrix n m R) :
    trace (A * single i j (1 : R)) = Aᵀ i j ∧
    trace (single i j (1 : R) * A) = Aᵀ i j := by

  simp_rw [eq_444, eq_445]
  simp [trace, updateCol_apply, updateRow_apply]

/--
> Assume $`\mathbf{A}` is $`n\times n`, $`\mathbf{J}` is $`n\times m` and $`\mathbf{B}` is $`m\times n`, then

  $$`\operatorname{Tr}(\mathbf{A}\mathbf{J}^{ij}\mathbf{B}) = (\mathbf{A}^T\mathbf{B}^T)_{ij} \tag{451}`
-/
theorem eq_451 (A : Matrix n n R) (i : n) (j : m) (B : Matrix m n R) :
    trace (A * single i j (1 : R) * B) = (Aᵀ * Bᵀ) i j := by
  conv_lhs => rw [← transpose_transpose A]
  simp_rw [trace, diag, ← eq_448]
  rfl

/--
> $$`\operatorname{Tr}(\mathbf{A}\mathbf{J}^{ji}\mathbf{B}) = (\mathbf{B}\mathbf{A})_{ij} \tag{452}`
-/
theorem eq_452 (A : Matrix n n R) (j : n) (i : m) (B : Matrix m n R) :
    trace (A * single j i (1 : R) * B) = (B * A) i j := by
  conv_lhs => rw [← transpose_transpose B]
  simp_rw [trace, diag, ← eq_449, mul_comm (A _ _)]
  rfl

/--
> $$`\operatorname{Tr}(\mathbf{A}\mathbf{J}^{ij}\mathbf{J}^{ij}\mathbf{B}) = \operatorname{diag}(\mathbf{A}^T\mathbf{B}^T)_{ij} \tag{453}`

The cookbook declares incompatible dimensions here; weassume the matrices are supposed to be
square.
-/
theorem eq_453 (A : Matrix n n R) (i : n) (j : n) (B : Matrix n n R) :
    trace (A * single i j (1 : R) * single i j (1 : R) * B) =
      diagonal (diag (Aᵀ * Bᵀ)) i j := by
  rw [mul_assoc _ _ B, mul_single_eq_updateCol_zero, MulOpposite.op_one, one_smul,
    single_mul_eq_updateRow_zero, one_smul]
  obtain rfl | hij := eq_or_ne i j
  · simp [Matrix.mul_apply, vecMulVec, trace]
  · simp [hij.symm, trace, hij]

/--
> Assume $`\mathbf{A}` is $`n\times n`, $`\mathbf{J}^{ij}` is $`n\times m` $`\mathbf{B}` is $`m\times n`, then

  $$`\mathbf{x}^T\mathbf{A}\mathbf{J}^{ij}\mathbf{B}\mathbf{x} = (\mathbf{A}^T\mathbf{x}\mathbf{x}^T\mathbf{B}^T)_{ij} \tag{454}`
-/
theorem eq_454 (A : Matrix n n R) (i : n) (j : m) (B : Matrix m n R) (x : n → R) :
    x ⬝ᵥ (A * single i j (1 : R) * B).mulVec x = (Aᵀ * vecMulVec x x * Bᵀ) i j := by
  simp_rw [dotProduct, mulVec, dotProduct, Finset.mul_sum, ← eq_446, mul_left_comm (x _),
    mul_right_comm _ (B _ _)]
  conv_rhs => simp [Matrix.mul_apply, vecMulVec, Finset.sum_mul]
  rw [Finset.sum_comm]

/--
> $$`\mathbf{x}^T\mathbf{A}\mathbf{J}^{ij}\mathbf{J}^{ij}\mathbf{B}\mathbf{x} = \operatorname{diag}(\mathbf{A}^T\mathbf{x}\mathbf{x}^T\mathbf{B}^T)_{ij} \tag{455}`

The cookbook declares incompatible dimensions here; weassume the matrices are supposed to be
square.
-/
theorem eq_455  (A : Matrix n n R) (i : n) (j : n) (B : Matrix n n R) (x : n → R) :
    x ⬝ᵥ (A * single i j (1 : R) * single i j (1 : R) * B).mulVec x =
      diagonal (diag (Aᵀ * vecMulVec x x * Bᵀ)) i j := by
  rw [mul_assoc _ _ B, mul_single_eq_updateCol_zero, MulOpposite.op_one, one_smul,
    single_mul_eq_updateRow_zero, one_smul]
  obtain rfl | hij := eq_or_ne i j
  · simp
    simp [dotProduct, vecMulVec, Matrix.mul_apply, mulVec, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    congr! 2 with j _ k _
    group
  · simp [hij.symm, hij]

/-!
### Structure Matrices
-/

/--
> The structure matrix is defined by

  $$`\frac{\partial\mathbf{A}}{\partial A_{ij}} = \mathbf{S}^{ij} \tag{456}`
-/
theorem eq_456 : (sorry : Prop) :=
  sorry

/--
> If $`\mathbf{A}` has no special structure then

  $$`\mathbf{S}^{ij} = \mathbf{J}^{ij} \tag{457}`
-/
theorem eq_457 : (sorry : Prop) :=
  sorry

/--
> If $`\mathbf{A}` is symmetric then

  $$`\mathbf{S}^{ij} = \mathbf{J}^{ij} + \mathbf{J}^{ji} - \mathbf{J}^{ij}\mathbf{J}^{ij} \tag{458}`
-/
theorem eq_458 : (sorry : Prop) :=
  sorry

/-!
## Symmetric, Skew-symmetric/Antisymmetric

### Symmetric
-/

/--
> The matrix $`\mathbf{A}` is said to be _symmetric_ if

  $$`\mathbf{A} = \mathbf{A}^T \tag{459}`
-/
theorem eq_459 (A : Matrix m m R) : A.IsSymm ↔ A = Aᵀ :=
  eq_comm

/-!
> Symmetric matrices have many important properties, e.g. that their eigenvalues are real and eigenvectors orthogonal.

### Skew-symmetric/Antisymmetric
-/

/--
> The _antisymmetric_ matrix is also known as the _skew_ symmetric matrix. It has the following property from which it is defined

  $$`\mathbf{A} = -\mathbf{A}^T \tag{460}`
-/
theorem eq_460 (A : Matrix m m R) : sorry ↔ A = -Aᵀ :=
  sorry

/--
> Hereby, it can be seen that the antisymmetric matrices always have a zero diagonal. The $`n\times n` antisymmetric matrices also have the following properties.

  $$`\det(\mathbf{A}^T) = \det(-\mathbf{A}) = (-1)^n\det(\mathbf{A}) \tag{461}`
-/
theorem eq_461 (A : Matrix m m R) (hA : A = -Aᵀ) : det Aᵀ = (-1) ^ Fintype.card m * det A := by
  rw [hA, transpose_neg, transpose_transpose, det_neg, ← hA]

/--
> $$`-\det(\mathbf{A}) = \det(-\mathbf{A}) = 0, \quad \text{if } n \text{ is odd} \tag{462}`
-/
theorem eq_462 (A : Matrix m m R) (hA : A = -Aᵀ) (hn : Odd (Fintype.card m)) :
    -det A = 0 ∧ det (-A) = 0 :=
  ⟨sorry, sorry⟩

/-!
> The eigenvalues of an antisymmetric matrix are placed on the imaginary axis and the eigenvectors are unitary.

### Decomposition
-/

/--
> A square matrix $`\mathbf{A}` can always be written as a sum of a symmetric $`\mathbf{A}_+` and an antisymmetric matrix $`\mathbf{A}_-`

  $$`\mathbf{A} = \mathbf{A}_+ + \mathbf{A}_- \tag{463}`
-/
theorem eq_463 : (sorry : Prop) :=
  sorry

/--
> Such a decomposition could e.g. be

  $$`\mathbf{A} = \frac{\mathbf{A}+\mathbf{A}^T}{2}+\frac{\mathbf{A}-\mathbf{A}^T}{2} = \mathbf{A}_+ + \mathbf{A}_- \tag{464}`
-/
theorem eq_464 : (sorry : Prop) :=
  sorry

/-!
## Toeplitz Matrices
-/

/--
> A Toeplitz matrix $`\mathbf{T}` is a matrix where the elements of each diagonal is the same. In the $`n\times n` square case, it has the following structure:

  $$`\mathbf{T} = \begin{bmatrix} t_{11} & t_{12} & \cdots & t_{1n} \\ t_{21} & \ddots & \ddots & \vdots \\ \vdots & \ddots & \ddots & t_{12} \\ t_{n1} & \cdots & t_{21} & t_{11} \end{bmatrix} = \begin{bmatrix} t_0 & t_1 & \cdots & t_{n-1} \\ t_{-1} & \ddots & \ddots & \vdots \\ \vdots & \ddots & \ddots & t_1 \\ t_{-(n-1)} & \cdots & t_{-1} & t_0 \end{bmatrix} \tag{465}`
-/
-- theorem is really a definition, so give an example
theorem eq_465 : toeplitz Subtype.val = !![0, 1, 2; -1, 0, 1; -2, -1, 0] :=
  Matrix.etaExpand_eq _ |>.symm

/--
> A Toeplitz matrix is _persymmetric_. If a matrix is persymmetric (or orthosymmetric), it means that the matrix is symmetric about its northeast-southwest diagonal (anti-diagonal) \[12\]. Persymmetric matrices is a larger class of matrices, since a persymmetric matrix not necessarily has a Toeplitz structure. There are some special cases of Toeplitz matrices. The _symmetric_ Toeplitz matrix is given by:

  $$`\mathbf{T} = \begin{bmatrix} t_0 & t_1 & \cdots & t_{n-1} \\ t_1 & \ddots & \ddots & \vdots \\ \vdots & \ddots & \ddots & t_1 \\ t_{n-1} & \cdots & t_1 & t_0 \end{bmatrix} \tag{466}`
-/
-- theorem is really a definition, so give an example
theorem eq_466 : toeplitzSymm ![0, 1, 2] = !![0, 1, 2; 1, 0, 1; 2, 1, 0] :=
  Matrix.etaExpand_eq _ |>.symm

/--
> The circular Toeplitz matrix:

  $$`\mathbf{T}_C = \begin{bmatrix} t_0 & t_1 & \cdots & t_{n-1} \\ t_{n-1} & \ddots & \ddots & \vdots \\ \vdots & \ddots & \ddots & t_1 \\ t_1 & \cdots & t_{n-1} & t_0 \end{bmatrix} \tag{467}`
-/
-- theorem is really a definition, so give an example
theorem eq_467 : toeplitzCirc ![0, 1, 2] = !![0, 1, 2; 2, 0, 1; 1, 2, 0] :=
  Matrix.etaExpand_eq _ |>.symm

/--
> The upper triangular Toeplitz matrix:

  $$`\mathbf{T}_U = \begin{bmatrix} t_0 & t_1 & \cdots & t_{n-1} \\ 0 & \ddots & \ddots & \vdots \\ \vdots & \ddots & \ddots & t_1 \\ 0 & \cdots & 0 & t_0 \end{bmatrix}, \tag{468}`
-/
-- theorem is really a definition, so give an example
theorem eq_468 : toeplitzUpper ![1, 2, 3] = !![1, 2, 3; 0, 1, 2; 0, 0, 1] :=
  Matrix.etaExpand_eq _ |>.symm

/--
> and the lower triangular Toeplitz matrix:

  $$`\mathbf{T}_L = \begin{bmatrix} t_0 & 0 & \cdots & 0 \\ t_{-1} & \ddots & \ddots & \vdots \\ \vdots & \ddots & \ddots & 0 \\ t_{-(n-1)} & \cdots & t_{-1} & t_0 \end{bmatrix} \tag{469}`
-/
-- theorem is really a definition, so give an example
theorem eq_469 : toeplitzLower ![1, 2, 3] = !![1, 0, 0; 2, 1, 0; 3, 2, 1] :=
  Matrix.etaExpand_eq _ |>.symm

/-!
### Properties of Toeplitz Matrices

> The Toeplitz matrix has some computational advantages. The addition of two Toeplitz matrices can be done with $`\mathcal{O}(n)` flops, multiplication of two Toeplitz matrices can be done in $`\mathcal{O}(n\ln n)` flops. Toeplitz equation systems can be solved in $`\mathcal{O}(n^2)` flops. The inverse of a positive definite Toeplitz matrix can be found in $`\mathcal{O}(n^2)` flops too. The inverse of a Toeplitz matrix is persymmetric. The product of two lower triangular Toeplitz matrices is a Toeplitz matrix. More information on Toeplitz matrices and circulant matrices can be found in \[13, 7\].

## Transition matrices

> A square matrix $`\mathbf{P}` is a transition matrix, also known as stochastic matrix or probability matrix, if

  $$`0 \leq (\mathbf{P})_{ij} \leq 1, \qquad \sum_j(\mathbf{P})_{ij} = 1`
-/

/--
> The transition matrix usually describes the probability of moving from state $`i` to $`j` in one step and is closely related to markov processes. Transition matrices have the following properties

  $$`\operatorname{Prob}[i\rightarrow j\text{ in 1 step}] = (\mathbf{P})_{ij} \tag{470}`
-/
theorem eq_470 : (sorry : Prop) :=
  sorry

/--
> $$`\operatorname{Prob}[i\rightarrow j\text{ in 2 steps}] = (\mathbf{P}^2)_{ij} \tag{471}`
-/
theorem eq_471 : (sorry : Prop) :=
  sorry

/--
> $$`\operatorname{Prob}[i\rightarrow j\text{ in }k\text{ steps}] = (\mathbf{P}^k)_{ij} \tag{472}`
-/
theorem eq_472 : (sorry : Prop) :=
  sorry

/--
> $$`\text{If all rows are identical} \quad\Rightarrow\quad \mathbf{P}^n = \mathbf{P} \tag{473}`
-/
theorem eq_473 : (sorry : Prop) :=
  sorry

/--
> $$`\boldsymbol{\alpha}\mathbf{P} = \boldsymbol{\alpha}, \qquad \boldsymbol{\alpha}\text{ is called invariant} \tag{474}`
-/
theorem eq_474 : (sorry : Prop) :=
  sorry

/-!
> where $`\boldsymbol{\alpha}` is a so-called stationary probability vector, i.e., $`0\leq\alpha_i\leq 1` and $`\sum_i\alpha_i = 1`.

## Units, Permutation and Shift

### Unit vector

> Let $`\mathbf{e}_i\in\mathbb{R}^{n\times 1}` be the $`i`th unit vector, i.e. the vector which is zero in all entries except the $`i`th at which it is 1.

### Rows and Columns
-/

/--
> $$`i.th\text{ row of }\mathbf{A} = \mathbf{e}_i^T\mathbf{A} \tag{475}`
-/
theorem eq_475 (A : Matrix m n R) (i) : A i = A.vecMul (Pi.single i 1) :=
  (single_one_vecMul _ _).symm

/--
> $$`j.th\text{ column of }\mathbf{A} = \mathbf{A}\mathbf{e}_j \tag{476}`
-/
theorem eq_476 (A : Matrix m n R) (j) : (fun i => A i j) = A.mulVec (Pi.single j 1) :=
  (mulVec_single_one _ _).symm

/-!
### Permutations
-/

/--
> Let $`\mathbf{P}` be some permutation matrix, e.g.

  $$`\mathbf{P} = \begin{bmatrix} 0 & 1 & 0 \\ 1 & 0 & 0 \\ 0 & 0 & 1 \end{bmatrix} = \begin{bmatrix} \mathbf{e}_2 & \mathbf{e}_1 & \mathbf{e}_3 \end{bmatrix} = \begin{bmatrix} \mathbf{e}_2^T \\ \mathbf{e}_1^T \\ \mathbf{e}_3^T \end{bmatrix} \tag{477}`
-/
theorem eq_477 :
    (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix _ _ R) =
      of ![(Pi.single 1 1 : Fin 3 → R), Pi.single 0 1, Pi.single 2 1] := by ext i j; fin_cases i <;> fin_cases j <;> rfl

/--
> For permutation matrices it holds that

  $$`\mathbf{P}\mathbf{P}^T = \mathbf{I} \tag{478}`
-/
theorem eq_478 (e : Equiv.Perm m) :
    e.toPEquiv.toMatrix * e.toPEquiv.toMatrixᵀ = (1 : Matrix m m R) := by
  rw [← PEquiv.toMatrix_symm, ← PEquiv.toMatrix_trans, ← Equiv.toPEquiv_symm, ←
    Equiv.toPEquiv_trans, Equiv.self_trans_symm, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl]

/--
> and that

  $$`\mathbf{A}\mathbf{P} = \begin{bmatrix} \mathbf{A}\mathbf{e}_2 & \mathbf{A}\mathbf{e}_1 & \mathbf{A}\mathbf{e}_3 \end{bmatrix} \qquad \mathbf{P}\mathbf{A} = \begin{bmatrix} \mathbf{e}_2^T\mathbf{A} \\ \mathbf{e}_1^T\mathbf{A} \\ \mathbf{e}_3^T\mathbf{A} \end{bmatrix} \tag{479}`
-/
theorem eq_479 : (sorry : Prop) :=
  sorry

/-!
> That is, the first is a matrix which has columns of $`\mathbf{A}` but in permuted sequence and the second is a matrix which has the rows of $`\mathbf{A}` but in the permuted sequence.

### Translation, Shift or Lag Operators
-/

/--
> Let $`\mathbf{L}` denote the lag (or 'translation' or 'shift') operator defined on a $`4\times 4` example by

  $$`\mathbf{L} = \begin{bmatrix} 0 & 0 & 0 & 0 \\ 1 & 0 & 0 & 0 \\ 0 & 1 & 0 & 0 \\ 0 & 0 & 1 & 0 \end{bmatrix} \tag{480}`
-/
theorem eq_480 : (sorry : Prop) :=
  sorry

/--
> i.e. a matrix of zeros with one on the sub-diagonal, $`(\mathbf{L})_{ij} = \delta_{i,j+1}`. With some signal $`x_t` for $`t = 1, ..., N`, the n.th power of the lag operator shifts the indices, i.e.

  $$`(\mathbf{L}^n\mathbf{x})_t = \left\{\begin{array}{ll} 0 & \text{for } t = 1, .., n \\ x_{t-n} & \text{for } t = n+1, ..., N \end{array}\right. \tag{481}`
-/
theorem eq_481 : (sorry : Prop) :=
  sorry

/--
> A related but slightly different matrix is the 'recurrent shifted' operator defined on a 4x4 example by

  $$`\hat{\mathbf{L}} = \begin{bmatrix} 0 & 0 & 0 & 1 \\ 1 & 0 & 0 & 0 \\ 0 & 1 & 0 & 0 \\ 0 & 0 & 1 & 0 \end{bmatrix} \tag{482}`
-/
theorem eq_482 : (sorry : Prop) :=
  sorry

/--
> i.e. a matrix defined by $`(\hat{\mathbf{L}})_{ij} = \delta_{i,j+1}+\delta_{i,1}\delta_{j,dim(\mathbf{L})}`. On a signal $`\mathbf{x}` it has the effect

  $$`(\hat{\mathbf{L}}^n\mathbf{x})_t = x_{t'}, \quad t' = [(t-n) \mod N]+1 \tag{483}`
-/
theorem eq_483 : (sorry : Prop) :=
  sorry

/--
> That is, $`\hat{\mathbf{L}}` is like the shift operator $`\mathbf{L}` except that it 'wraps' the signal as if it was periodic and shifted (substituting the zeros with the rear end of the signal). Note that $`\hat{\mathbf{L}}` is invertible and orthogonal, i.e.

  $$`\hat{\mathbf{L}}^{-1} = \hat{\mathbf{L}}^T \tag{484}`
-/
theorem eq_484 : (sorry : Prop) :=
  sorry

/-!
## Vandermonde Matrices
-/

/--
> A Vandermonde matrix has the form \[15\]

  $$`\mathbf{V} = \begin{bmatrix} 1 & v_1 & v_1^2 & \cdots & v_1^{n-1} \\ 1 & v_2 & v_2^2 & \cdots & v_2^{n-1} \\ \vdots & \vdots & \vdots & & \vdots \\ 1 & v_n & v_n^2 & \cdots & v_n^{n-1} \end{bmatrix}. \tag{485}`
-/
theorem eq_485 {n : ℕ} (v : Fin n → R) (i j : Fin n) : vandermonde v i j = v i ^ (j : ℕ) :=
  vandermonde_apply _ _ _

/--
> The transpose of $`\mathbf{V}` is also said to a Vandermonde matrix. The determinant is given by \[29\]

  $$`\det\mathbf{V} = \prod_{i>j}(v_i-v_j) \tag{486}`
-/
theorem eq_486 {n : ℕ} (v : Fin n → R) :
    det (vandermonde v) = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (v j - v i) :=
  det_vandermonde _

end MatrixCookbook
