import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Matrix
import Mathlib.Data.Matrix.Kronecker
import Mathlib.Data.Matrix.Hadamard
import Mathlib.Topology.UniformSpace.Matrix

/-! # Missing lemmas about matrix analysis -/


variable {ι : Type _} {R : Type _} {A : Type _} {m n p q : Type _}

variable [Fintype m] [Fintype n] [Fintype p] [Fintype q]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

open Matrix

open scoped Matrix Kronecker

/-! ### Lemmas about the sup norm on matrices

Note that for each choice of norm, all the lemmas must be repeated...

https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Topology.20on.20continuous_maps.20without.20a.20norm/near/359326930
-/


section SupNorm

variable [NontriviallyNormedField R] [NormedRing A] [NormedAlgebra R A]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

-- `matrix.normed_space` is about `semi_normed_group` which massively impacts the performance of
-- typeclass search in later lemmas.
@[local instance]
def matrixFieldNormedSpace : NormedSpace R (Matrix m n R) :=
  Matrix.normedSpace

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

-- This is only about the elementwise norm...
theorem deriv_matrix (f : R → Matrix m n A) (r : R) (hX : DifferentiableAt R f r) :
    deriv f r = of fun i j => deriv (fun r => f r i j) r := by
  ext i j
  rw [of_apply, deriv_pi]
  dsimp only
  rw [deriv_pi]
  · intro i
    erw [differentiableAt_pi] at hX -- porting note: added
    simp_rw [differentiableAt_pi] at hX
    apply hX
  · intro i
    rw [differentiableAt_pi] at hX
    apply hX

end SupNorm

section LinftyOpNorm

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable [NontriviallyNormedField R] [NormedCommRing A] [NormedAlgebra R A] [CompleteSpace A]

theorem HasDerivAt.matrix_inv {X : R → Matrix m m A} {X' : Matrix m m A} {r : R}
    (hX : HasDerivAt X X' r) (hX' : IsUnit (X r)) :
    HasDerivAt (fun a => (X a)⁻¹) (-(X r)⁻¹ * X' * (X r)⁻¹) r := by
  simp_rw [nonsing_inv_eq_ringInverse]
  obtain ⟨u, hu⟩ := hX'
  have : HasFDerivAt _ (_ : _ →L[R] _) _ := hasFDerivAt_ringInverse u
  simp_rw [← Ring.inverse_unit u, hu] at this
  rw [hasDerivAt_iff_hasFDerivAt] at hX ⊢
  convert HasFDerivAt.comp _ this hX
  ext r : 2 -- porting note: added one!
  -- porting note: added `()`-wrapped lemmas
  simp [Matrix.mul_smul, (ContinuousLinearMap.smulRight_apply), (ContinuousLinearMap.comp_apply), (ContinuousLinearMap.neg_apply)]

end LinftyOpNorm
