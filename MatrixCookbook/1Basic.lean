module

public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Basic.NNReal.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.SchurComplement
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.Topology.MetricSpace.Basic
public import MatrixCookbook.Lib.TraceDetFinFour

set_option doc.verso true

/-!
# Basics

This chapter collects elementary identities about inverses, transposes, conjugate transposes,
traces and determinants.
Text and equations quoted from _The Matrix Cookbook_ are set in a serif face; on wide screens
they fill the left-hand column. Everything else, including the Lean statements and proofs, is
commentary on the formalization.

Throughout, matrices ({name}`Matrix`) have entries in a field {lit}`R`, and are indexed by
arbitrary finite types ({lit}`m`, {lit}`n`, {lit}`p`) rather than by {lit}`Fin n`, except where
the cookbook specializes to small sizes.
Mathlib's inverse {lit}`A⁻¹` ({name}`Matrix.inv_def`) is defined for every square matrix,
returning {lit}`0` when {lit}`A` is singular, so most of these identities hold without any
invertibility hypothesis.
-/

public section

variable {ι : Type _} {R : Type _} {m n p : Type _}

variable [Fintype m] [Fintype n] [Fintype p]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p]

namespace MatrixCookbook

open scoped Matrix BigOperators Filter Topology

open Matrix

variable [Field R]

/--
> $$`(\mathbf{A}\mathbf{B})^{-1} = \mathbf{B}^{-1}\mathbf{A}^{-1} \tag{1}`
-/
theorem eq_1 {A : Matrix m m R} {B : Matrix m m R} : (A * B)⁻¹ = B⁻¹ * A⁻¹ :=
  Matrix.mul_inv_rev _ _

/--
> $$`(\mathbf{A}\mathbf{B}\mathbf{C}\ldots)^{-1} = \ldots\mathbf{C}^{-1}\mathbf{B}^{-1}\mathbf{A}^{-1} \tag{2}`

Stated for an arbitrary list of matrices.
-/
theorem eq_2 {l : List (Matrix m m R)} : l.prod⁻¹ = (l.reverse.map Inv.inv).prod :=
  Matrix.list_prod_inv_reverse _

/--
> $$`(\mathbf{A}^T)^{-1} = (\mathbf{A}^{-1})^T \tag{3}`
-/
theorem eq_3 {A : Matrix m m R} : Aᵀ⁻¹ = A⁻¹ᵀ :=
  (transpose_nonsing_inv _).symm

/--
> $$`(\mathbf{A}+\mathbf{B})^T = \mathbf{A}^T+\mathbf{B}^T \tag{4}`
-/
theorem eq_4 {A B : Matrix m n R} : (A + B)ᵀ = Aᵀ + Bᵀ :=
  transpose_add _ _

/--
> $$`(\mathbf{A}\mathbf{B})^T = \mathbf{B}^T\mathbf{A}^T \tag{5}`
-/
theorem eq_5 {A : Matrix m n R} {B : Matrix n p R} : (A * B)ᵀ = Bᵀ * Aᵀ :=
  transpose_mul _ _

/--
> $$`(\mathbf{A}\mathbf{B}\mathbf{C}\ldots)^T = \ldots\mathbf{C}^T\mathbf{B}^T\mathbf{A}^T \tag{6}`

Stated for an arbitrary list of matrices.
-/
theorem eq_6 {l : List (Matrix m m R)} : l.prodᵀ = (l.map transpose).reverse.prod :=
  Matrix.transpose_list_prod _

/--
> $$`(\mathbf{A}^H)^{-1} = (\mathbf{A}^{-1})^H \tag{7}`
-/
theorem eq_7 [StarRing R] {A : Matrix m m R} : Aᴴ⁻¹ = A⁻¹ᴴ :=
  (conjTranspose_nonsing_inv _).symm

/--
> $$`(\mathbf{A}+\mathbf{B})^H = \mathbf{A}^H+\mathbf{B}^H \tag{8}`
-/
theorem eq_8 [StarRing R] {A B : Matrix m n R} : (A + B)ᴴ = Aᴴ + Bᴴ :=
  conjTranspose_add _ _

/--
> $$`(\mathbf{A}\mathbf{B})^H = \mathbf{B}^H\mathbf{A}^H \tag{9}`
-/
theorem eq_9 [StarRing R] {A : Matrix m n R} {B : Matrix n p R} : (A * B)ᴴ = Bᴴ * Aᴴ :=
  conjTranspose_mul _ _

/--
> $$`(\mathbf{A}\mathbf{B}\mathbf{C}\ldots)^H = \ldots\mathbf{C}^H\mathbf{B}^H\mathbf{A}^H \tag{10}`

Stated for an arbitrary list of matrices.
-/
theorem eq_10 [StarRing R] {l : List (Matrix m m R)} :
    l.prodᴴ = (l.map conjTranspose).reverse.prod :=
  Matrix.conjTranspose_list_prod _

/-! ## Trace -/


section

/--
> $$`\operatorname{Tr}(\mathbf{A}) = \sum_i A_{ii} \tag{11}`
-/
theorem eq_11 {A : Matrix m m R} : trace A = ∑ i, A i i :=
  rfl

/--
> $$`\operatorname{Tr}(\mathbf{A}) = \sum_i \lambda_i, \quad \lambda_i = \operatorname{eig}(\mathbf{A}) \tag{12}`

The eigenvalues are the roots of the characteristic polynomial, so this needs an
algebraically closed field.
-/
theorem eq_12 {A : Matrix m m R} [IsAlgClosed R] : trace A = A.charpoly.roots.sum :=
  trace_eq_sum_roots_charpoly _

/--
> $$`\operatorname{Tr}(\mathbf{A}) = \operatorname{Tr}(\mathbf{A}^T) \tag{13}`
-/
theorem eq_13 {A : Matrix m m R} : trace A = trace Aᵀ :=
  (Matrix.trace_transpose _).symm

/--
> $$`\operatorname{Tr}(\mathbf{A}\mathbf{B}) = \operatorname{Tr}(\mathbf{B}\mathbf{A}) \tag{14}`
-/
theorem eq_14 {A : Matrix m n R} {B : Matrix n m R} : trace (A * B) = trace (B * A) :=
  Matrix.trace_mul_comm _ _

/--
> $$`\operatorname{Tr}(\mathbf{A}+\mathbf{B}) = \operatorname{Tr}(\mathbf{A})+\operatorname{Tr}(\mathbf{B}) \tag{15}`
-/
theorem eq_15 {A B : Matrix m m R} : trace (A + B) = trace A + trace B :=
  trace_add _ _

/--
> $$`\operatorname{Tr}(\mathbf{A}\mathbf{B}\mathbf{C}) = \operatorname{Tr}(\mathbf{B}\mathbf{C}\mathbf{A}) = \operatorname{Tr}(\mathbf{C}\mathbf{A}\mathbf{B}) \tag{16}`
-/
theorem eq_16 {A : Matrix m n R} {B : Matrix n p R} {C : Matrix p m R} :
    trace (A * B * C) = trace (B * C * A) :=
  (Matrix.trace_mul_cycle B C A).symm

/--
> $$`\mathbf{a}^T\mathbf{a} = \operatorname{Tr}(\mathbf{a}\mathbf{a}^T) \tag{17}`

Mathlib writes the column vector as {lit}`replicateCol Unit a` (see {name}`Matrix.replicateCol`).
-/
theorem eq_17 {a : m → R} : dotProduct a a = trace (replicateCol Unit a * replicateRow Unit a) :=
  (Matrix.trace_replicateCol_mul_replicateRow _ _).symm

end

/-! ## Determinant

> Let $`\mathbf{A}` be an $`n \times n` matrix.
-/


-- `matrix.is_hermitian.det_eq_prod_eigenvalues` is close, but needs `A` to be hermitian which is too strong
/--
> $$`\det(\mathbf{A}) = \prod_i \lambda_i \qquad \lambda_i = \operatorname{eig}(\mathbf{A}) \tag{18}`

As for (12), this needs an algebraically closed field.
-/
theorem eq_18 {A : Matrix m m R} [IsAlgClosed R] : det A = A.charpoly.roots.prod :=
  det_eq_prod_roots_charpoly _

/--
> $$`\det(c\mathbf{A}) = c^n \det(\mathbf{A}), \quad \text{if } \mathbf{A} \in \mathbb{R}^{n \times n} \tag{19}`
-/
theorem eq_19 (c : R) {A : Matrix m m R} : det (c • A) = c ^ Fintype.card m * det A :=
  det_smul _ _

/--
> $$`\det(\mathbf{A}^T) = \det(\mathbf{A}) \tag{20}`
-/
theorem eq_20 {A : Matrix m m R} : det Aᵀ = det A :=
  det_transpose _

/--
> $$`\det(\mathbf{A}\mathbf{B}) = \det(\mathbf{A})\det(\mathbf{B}) \tag{21}`
-/
theorem eq_21 {A B : Matrix m m R} : det (A * B) = det A * det B :=
  det_mul _ _

/--
> $$`\det(\mathbf{A}^{-1}) = 1/\det(\mathbf{A}) \tag{22}`
-/
theorem eq_22 {A : Matrix m m R} : det A⁻¹ = (det A)⁻¹ :=
  (det_nonsing_inv _).trans (Ring.inverse_eq_inv _)

/--
> $$`\det(\mathbf{A}^n) = \det(\mathbf{A})^n \tag{23}`
-/
theorem eq_23 {A : Matrix m m R} (k : ℕ) : det (A ^ k) = det A ^ k :=
  det_pow _ _

/--
> $$`\det(\mathbf{I}+\mathbf{u}\mathbf{v}^T) = 1+\mathbf{u}^T\mathbf{v} \tag{24}`
-/
theorem eq_24 {u v : m → R} : det (1 + replicateCol Unit u * replicateRow Unit v) = 1 + dotProduct u v := by
  rw [det_one_add_replicateCol_mul_replicateRow u v, dotProduct_comm]

/--
> For $`n = 2`:

  $$`\det(\mathbf{I}+\mathbf{A}) = 1+\det(\mathbf{A})+\operatorname{Tr}(\mathbf{A}) \tag{25}`
-/
theorem eq_25 {A : Matrix (Fin 2) (Fin 2) R} : det (1 + A) = 1 + det A + trace A := by
  simp [det_fin_two, trace_fin_two]; ring

/--
> For $`n = 3`:

  $$`\begin{aligned}\det(\mathbf{I}+\mathbf{A}) = {}& 1+\det(\mathbf{A})+\operatorname{Tr}(\mathbf{A}) \\ &+\tfrac{1}{2}\operatorname{Tr}(\mathbf{A})^2-\tfrac{1}{2}\operatorname{Tr}(\mathbf{A}^2)\end{aligned} \tag{26}`
-/
theorem eq_26 {A : Matrix (Fin 3) (Fin 3) R} [Invertible (2 : R)] :
    det (1 + A) = 1 + det A + trace A + ⅟ 2 * trace A ^ 2 - ⅟ 2 * trace (A ^ 2) := by
  apply mul_left_cancel₀ (isUnit_of_invertible (2 : R)).ne_zero
  simp only [det_fin_three, trace_fin_three, pow_two, Matrix.mul_apply,
    Fin.sum_univ_succ]
  dsimp
  simp only [mul_add, mul_sub, mul_invOf_cancel_left]
  simp_rw [Matrix.one_apply]
  simp (config := {decide := true})
  ring

/--
> For $`n = 4`:

  $$`\begin{aligned}\det(\mathbf{I}+\mathbf{A}) &= 1+\det(\mathbf{A})+\operatorname{Tr}(\mathbf{A})+\frac{1}{2} \\ &\quad +\operatorname{Tr}(\mathbf{A})^2-\frac{1}{2}\operatorname{Tr}(\mathbf{A}^2) \\ &\quad +\frac{1}{6}\operatorname{Tr}(\mathbf{A})^3-\frac{1}{2}\operatorname{Tr}(\mathbf{A})\operatorname{Tr}(\mathbf{A}^2)+\frac{1}{3}\operatorname{Tr}(\mathbf{A}^3)\end{aligned} \tag{27}`

As printed, the $`\frac{1}{2}` ending the first line belongs to the
$`\operatorname{Tr}(\mathbf{A})^2` term that starts the second. The theorem below states the
intended formula.
-/
theorem eq_27 {A : Matrix (Fin 4) (Fin 4) R} [CharZero R] :
    det (1 + A) =
      1 + det A + trace A + 1 / 2 * (trace A ^ 2 - trace (A ^ 2)) +
        1 / 6 * (trace A ^ 3 - 3 * trace A * trace (A ^ 2) + 2 * trace (A ^ 3)) := by
  -- TODO: it might be cleaner to prove this via the
  -- [Girard-Waring formula](https://math.stackexchange.com/a/2779104/1896), which wouldn't produce
  -- such a frighteniningly long goal state!
  field_simp
  rw [det_one_add_fin_four, det_fin_four, trace_pow_three_fin_four, trace_pow_two_fin_four,
    sq_trace_fin_four, trace_fin_four]
  ring

-- TODO: is this statement correct?
/--
> For small $`\varepsilon`, the following approximation holds

  $$`\begin{aligned}\det(\mathbf{I}+\varepsilon\mathbf{A}) \cong {}& 1+\det(\mathbf{A})+\varepsilon\operatorname{Tr}(\mathbf{A}) \\ &+\tfrac{1}{2}\varepsilon^2\operatorname{Tr}(\mathbf{A})^2-\tfrac{1}{2}\varepsilon^2\operatorname{Tr}(\mathbf{A}^2)\end{aligned} \tag{28}`

It is not clear what the precise statement should be, and the $`\det(\mathbf{A})` term looks
wrong in the source material.
This is one candidate formalization, as a statement about real $`\varepsilon` near zero; the next
theorem is another, about formal power series truncated at order 2.
Neither is proved yet.
-/
theorem eq_28 {A : Matrix n n ℝ} :
    (fun ε : NNReal => det (1 + ε • A)) =ᶠ[Filter.atBot] fun ε =>
      1 + det A + ε * trace A + 1 / 2 * ε ^ 2 * trace A ^ 2 - 1 / 2 * ε ^ 2 * trace (A ^ 2) :=
  sorry

-- TODO: or is this statement correct?
theorem eq_28' {A : Matrix n n R} :
    let ε : PowerSeries R := PowerSeries.X
    let A : Matrix n n (PowerSeries R) := A.map PowerSeries.C
    (det (1 + ε • A)).trunc 2 =
      (1 + det A + ε • trace A + (1 / 2 : R) • ε ^ 2 * trace A ^ 2 -
            (1 / 2 : R) • ε ^ 2 * trace (A ^ 2)).trunc
        2 :=
  sorry

/-!
## The Special Case 2x2

> Consider the matrix $`\mathbf{A}`

  $$`\mathbf{A} = \begin{bmatrix} A_{11} & A_{12} \\ A_{21} & A_{22} \end{bmatrix}`

In Lean, {lit}`A : Matrix (Fin 2) (Fin 2) R`, and indices start from {lit}`0` rather than {lit}`1`.
-/


section

/--
> Determinant and trace

  $$`\det(\mathbf{A}) = A_{11}A_{22}-A_{12}A_{21} \tag{29}`
-/
theorem eq_29 {A : Matrix (Fin 2) (Fin 2) R} : det A = A 0 0 * A 1 1 - A 0 1 * A 1 0 :=
  det_fin_two _

/--
> $$`\operatorname{Tr}(\mathbf{A}) = A_{11}+A_{22} \tag{30}`
-/
theorem eq_30 {A : Matrix (Fin 2) (Fin 2) R} : trace A = A 0 0 + A 1 1 :=
  trace_fin_two _

/-!
> Eigenvalues

  $$`\lambda^2 - \lambda \cdot \operatorname{Tr}(\mathbf{A}) + \det(\mathbf{A}) = 0`

  $$`\lambda_1 = \frac{\operatorname{Tr}(\mathbf{A}) + \sqrt{\operatorname{Tr}(\mathbf{A})^2 - 4\det(\mathbf{A})}}{2}`

  $$`\lambda_2 = \frac{\operatorname{Tr}(\mathbf{A}) - \sqrt{\operatorname{Tr}(\mathbf{A})^2 - 4\det(\mathbf{A})}}{2}`

  $$`\lambda_1 + \lambda_2 = \operatorname{Tr}(\mathbf{A}) \qquad \lambda_1\lambda_2 = \det(\mathbf{A})`

  Eigenvectors

  $$`\mathbf{v}_1 \propto \begin{bmatrix} A_{12} \\ \lambda_1 - A_{11} \end{bmatrix} \qquad \mathbf{v}_2 \propto \begin{bmatrix} A_{12} \\ \lambda_2 - A_{11} \end{bmatrix}`

The eigenvalue and eigenvector facts are not yet formalized.
-/


/--
> Inverse

  $$`\mathbf{A}^{-1} = \frac{1}{\det(\mathbf{A})}\begin{bmatrix} A_{22} & -A_{12} \\ -A_{21} & A_{11} \end{bmatrix} \tag{31}`
-/
theorem eq_31 {A : Matrix (Fin 2) (Fin 2) R} : A⁻¹ = (det A)⁻¹ • !![A 1 1, -A 0 1; -A 1 0, A 0 0] := by
  rw [inv_def, adjugate_fin_two, Ring.inverse_eq_inv]

end

end MatrixCookbook
