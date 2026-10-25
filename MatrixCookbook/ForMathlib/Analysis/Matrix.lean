module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Star
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Hadamard
public import Mathlib.Topology.UniformSpace.Matrix

/-! # Missing lemmas about matrix analysis -/

@[expose] public section

variable {ι : Type _} {R : Type _} {A : Type _} {m n p q : Type _}

variable [Fintype m] [Fintype n] [Fintype p] [Fintype q]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

open Matrix

open scoped Matrix Kronecker

/-! ### Lemmas about derivatives of matrices

These statements only depend on the topology on matrices, so hold for any choice of matrix norm;
the proofs pick whichever norm is most convenient.
-/


section

variable [NontriviallyNormedField R] [NormedRing A] [NormedAlgebra R A]

theorem hasDerivAt_matrix {f : R → Matrix m n A} {r : R} {f' : Matrix m n A} :
    HasDerivAt f f' r ↔ ∀ i j, HasDerivAt (fun r => f r i j) (f' i j) r := by
  erw [hasDerivAt_pi]
  simp_rw [hasDerivAt_pi]

theorem HasDerivAt.matrix_mul {X : R → Matrix m n A} {Y : R → Matrix n p A} {X' : Matrix m n A}
    {Y' : Matrix n p A} {r : R} (hX : HasDerivAt X X' r) (hY : HasDerivAt Y Y' r) :
    HasDerivAt (fun a => X a * Y a) (X' * Y r + X r * Y') r := by
  rw [hasDerivAt_matrix] at hX hY ⊢
  intro i j
  simp only [mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib]
  exact HasDerivAt.fun_sum fun k _hk => (hX _ _).fun_mul (hY _ _)

theorem HasDerivAt.matrix_kronecker {X : R → Matrix m n A} {Y : R → Matrix p q A}
    {X' : Matrix m n A} {Y' : Matrix p q A} {r : R} (hX : HasDerivAt X X' r)
    (hY : HasDerivAt Y Y' r) : HasDerivAt (fun a => X a ⊗ₖ Y a) (X' ⊗ₖ Y r + X r ⊗ₖ Y') r := by
  rw [hasDerivAt_matrix] at hX hY ⊢
  rintro ⟨i, i'⟩ ⟨j, j'⟩
  exact (hX _ _).mul (hY _ _)

theorem HasDerivAt.matrix_hadamard {X Y : R → Matrix m n A} {X' Y' : Matrix m n A} {r : R}
    (hX : HasDerivAt X X' r) (hY : HasDerivAt Y Y' r) :
    HasDerivAt (fun a => X a ⊙ Y a) (X' ⊙ Y r + X r ⊙ Y') r := by
  rw [hasDerivAt_matrix] at hX hY ⊢
  rintro i j
  exact (hX _ _).mul (hY _ _)

theorem HasDerivAt.trace {X : R → Matrix m m A} {X' : Matrix m m A} {r : R}
    (hX : HasDerivAt X X' r) : HasDerivAt (fun a => (X a).trace) X'.trace r :=
  HasDerivAt.fun_sum fun i _hi => (hasDerivAt_matrix.mp hX : _) i i

theorem HasDerivAt.transpose {X : R → Matrix m n A} {X' : Matrix m n A} {r : R}
    (hX : HasDerivAt X X' r) : HasDerivAt (fun a => (X a)ᵀ) X'ᵀ r :=
  hasDerivAt_matrix.mpr fun i j => (hasDerivAt_matrix.mp hX : _) j i

theorem HasDerivAt.conjTranspose [StarRing R] [TrivialStar R] [StarAddMonoid A] [StarModule R A]
    [ContinuousStar A] {X : R → Matrix m n A} {X' : Matrix m n A} {r : R} (hX : HasDerivAt X X' r) :
    HasDerivAt (fun a => (X a)ᴴ) X'ᴴ r :=
  hasDerivAt_matrix.mpr fun i j => ((hasDerivAt_matrix.mp hX : _) j i).star

theorem deriv_matrix (f : R → Matrix m n A) (r : R) (hX : DifferentiableAt R f r) :
    deriv f r = of fun i j => deriv (fun r => f r i j) r := by
  open scoped Matrix.Norms.Elementwise in
  ext i j
  rw [of_apply]
  exact ((hasDerivAt_matrix.mp hX.hasDerivAt) i j).deriv.symm

end

section

variable [NontriviallyNormedField R] [NormedCommRing A] [NormedAlgebra R A] [CompleteSpace A]

theorem HasDerivAt.matrix_inv {X : R → Matrix m m A} {X' : Matrix m m A} {r : R}
    (hX : HasDerivAt X X' r) (hX' : IsUnit (X r)) :
    HasDerivAt (fun a => (X a)⁻¹) (-(X r)⁻¹ * X' * (X r)⁻¹) r := by
  open scoped Matrix.Norms.Operator in
  -- The uniform structure from the operator norm only agrees with `Matrix.instUniformSpace` at
  -- default transparency, so this is not found automatically.
  have : HasSummableGeomSeries (Matrix m m A) :=
    @instHasSummableGeomSeriesOfCompleteSpace _ _ (inferInstanceAs (CompleteSpace (Matrix m m A)))
  obtain ⟨u, hu⟩ := hX'
  have h1 : HasFDerivAt (𝕜 := R) Ring.inverse _ (X r) := hu ▸ hasFDerivAt_ringInverse u
  have h := HasFDerivAt.comp_hasDerivAt (x := r) h1 hX
  simp_rw [nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit] at h ⊢
  refine h.congr_deriv ?_
  simp

end
