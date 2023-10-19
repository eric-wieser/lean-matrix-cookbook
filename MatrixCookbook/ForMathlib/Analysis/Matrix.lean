import analysis.calculus.deriv.add
import analysis.calculus.deriv.mul
import analysis.calculus.deriv.prod
import analysis.calculus.deriv.star
import analysis.matrix
import data.matrix.kronecker
import data.matrix.hadamard
import topology.uniform_space.matrix 

/-! # Missing lemmas about matrix analysis -/

variables {ι : Type*} {R : Type*} {A : Type*} {m n p q : Type*}
variables [fintype m] [fintype n] [fintype p] [fintype q]
variables [decidable_eq m] [decidable_eq n] [decidable_eq p] [decidable_eq q]

open matrix
open_locale matrix kronecker

/-! ### Lemmas about the sup norm on matrices

Note that for each choice of norm, all the lemmas must be repeated...

https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Topology.20on.20continuous_maps.20without.20a.20norm/near/359326930
-/
section sup_norm
variables [nontrivially_normed_field R] [normed_ring A] [normed_algebra R A]

local attribute [instance] matrix.normed_add_comm_group matrix.normed_space
-- `matrix.normed_space` is about `semi_normed_group` which massively impacts the performance of
-- typeclass search in later lemmas.
local attribute [instance]
def matrix_field_normed_space : normed_space R (matrix m n R) :=
by exact matrix.normed_space

lemma has_deriv_at_matrix {f : R → matrix m n A} {r : R} {f' : matrix m n A} :
  has_deriv_at f f' r ↔ (∀ i j, has_deriv_at (λ r, f r i j) (f' i j) r) :=
by simp_rw has_deriv_at_pi

lemma has_deriv_at.matrix_mul {X : R → matrix m n A} {Y : R → matrix n p A}
  {X' : matrix m n A} {Y' : matrix n p A} {r : R}
  (hX : has_deriv_at X X' r) (hY : has_deriv_at Y Y' r) :
  has_deriv_at (λ a, (X a) ⬝ (Y a)) (X' ⬝ Y r + X r ⬝ Y') r :=
begin
  rw has_deriv_at_matrix at ⊢ hX hY,
  intros i j,
  simp only [mul_apply, pi.add_apply, ←finset.sum_add_distrib],
  exact has_deriv_at.sum (λ k hk, (hX _ _).mul (hY _ _)),
end

lemma has_deriv_at.matrix_kronecker {X : R → matrix m n A} {Y : R → matrix p q A}
  {X' : matrix m n A} {Y' : matrix p q A} {r : R}
  (hX : has_deriv_at X X' r) (hY : has_deriv_at Y Y' r) :
  has_deriv_at (λ a, (X a) ⊗ₖ (Y a)) (X' ⊗ₖ Y r + X r ⊗ₖ Y') r :=
begin
  rw has_deriv_at_matrix at ⊢ hX hY,
  rintros ⟨i, i'⟩ ⟨j, j'⟩,
  exact (hX _ _).mul (hY _ _),
end

lemma has_deriv_at.matrix_hadamard {X Y : R → matrix m n A}
  {X' Y' : matrix m n A} {r : R}
  (hX : has_deriv_at X X' r) (hY : has_deriv_at Y Y' r) :
  has_deriv_at (λ a, (X a) ⊙ (Y a)) (X' ⊙ Y r + X r ⊙ Y') r :=
begin
  rw has_deriv_at_matrix at ⊢ hX hY,
  rintros i j,
  exact (hX _ _).mul (hY _ _),
end

lemma has_deriv_at.trace {X : R → matrix m m A} {X' : matrix m m A} {r : R}
  (hX : has_deriv_at X X' r) :
  has_deriv_at (λ a, (X a).trace) X'.trace r :=
has_deriv_at.sum $ λ i hi, (has_deriv_at_matrix.mp hX : _) i i

lemma has_deriv_at.transpose {X : R → matrix m n A} {X' : matrix m n A} {r : R}
  (hX : has_deriv_at X X' r) :
  has_deriv_at (λ a, (X a)ᵀ) X'ᵀ r :=
has_deriv_at_matrix.mpr $ λ i j, (has_deriv_at_matrix.mp hX : _) j i

lemma has_deriv_at.conj_transpose
  [star_ring R] [has_trivial_star R] [star_add_monoid A] [star_module R A] [has_continuous_star A]
  {X : R → matrix m n A} {X' : matrix m n A} {r : R}
  (hX : has_deriv_at X X' r) :
  has_deriv_at (λ a, (X a)ᴴ) X'ᴴ r :=
has_deriv_at_matrix.mpr $ λ i j, ((has_deriv_at_matrix.mp hX : _) j i).star

-- This is only about the elementwise norm...
lemma deriv_matrix (f : R → matrix m n A) (r : R) (hX : differentiable_at R f r) :
  deriv f r = of (λ i j, deriv (λ r, f r i j) r) :=
begin
  ext i j,
  rw deriv_pi,
  simp_rw [deriv_pi, of_apply],
  rw deriv_pi,
  { intro i,
    simp_rw differentiable_at_pi at hX,
    apply hX },
  { intro i,
    rw differentiable_at_pi at hX,
    apply hX },
end

end sup_norm

section linfty_op_norm
local attribute [instance] matrix.linfty_op_normed_ring matrix.linfty_op_normed_algebra
variables [nontrivially_normed_field R] [normed_comm_ring A] [normed_algebra R A] [complete_space A]

lemma has_deriv_at.matrix_inv {X : R → matrix m m A} {X' : matrix m m A} {r : R}
  (hX : has_deriv_at X X' r) (hX' : is_unit (X r)) :
  has_deriv_at (λ a, (X a)⁻¹) (-(X r)⁻¹ * X' * (X r)⁻¹) r :=
begin
  simp_rw nonsing_inv_eq_ring_inverse,
  obtain ⟨u, hu⟩ := hX',
  have : has_fderiv_at _ (_ : _ →L[R] _) _ := has_fderiv_at_ring_inverse u,
  simp_rw [←ring.inverse_unit u, hu, ←ring.inverse_unit u, hu] at this,
  rw has_deriv_at_iff_has_fderiv_at at ⊢ hX,
  convert has_fderiv_at.comp _ this hX ,
  ext1 r,
  simp [matrix.mul_smul],
end

end linfty_op_norm
