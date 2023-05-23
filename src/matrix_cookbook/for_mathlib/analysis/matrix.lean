/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

import analysis.matrix
import data.matrix.kronecker
import data.matrix.hadamard

/-! # Missing lemmas about matrix analysis -/

variables {ι : Type*} {R : Type*} {m n p q : Type*}
variables [fintype m] [fintype n] [fintype p] [fintype q]
variables [decidable_eq m] [decidable_eq n] [decidable_eq p] [decidable_eq q]
variables [nontrivially_normed_field R]

open matrix
open_locale matrix kronecker

/-! ### Lemmas about the sup norm on matrices

Note that for each choice of norm, all the lemmas must be repeated...

https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Topology.20on.20continuous_maps.20without.20a.20norm/near/359326930
-/
section sup_norm

local attribute [instance] matrix.normed_add_comm_group matrix.normed_space
-- `matrix.normed_space` is about `semi_normed_group` which massively impacts the performance of
-- typeclass search in later lemmas.
local attribute [instance]
def matrix_field_normed_space : normed_space R (matrix m n R) :=
by exact matrix.normed_space

lemma has_deriv_at_matrix {f : R → matrix m n R} {r : R} {f' : matrix m n R} :
  has_deriv_at f f' r ↔ (∀ i j, has_deriv_at (λ r, f r i j) (f' i j) r) :=
by simp_rw has_deriv_at_pi

lemma has_deriv_at.matrix_mul {X : R → matrix m n R} {Y : R → matrix n p R}
  {X' : matrix m n R} {Y' : matrix n p R} {r : R}
  (hX : has_deriv_at X X' r) (hY : has_deriv_at Y Y' r) :
  has_deriv_at (λ a, (X a) ⬝ (Y a)) (X' ⬝ Y r + X r ⬝ Y') r :=
begin
  rw has_deriv_at_matrix at ⊢ hX hY,
  intros i j,
  simp only [mul_apply, pi.add_apply, ←finset.sum_add_distrib],
  exact has_deriv_at.sum (λ k hk, (hX _ _).mul (hY _ _)),
end

lemma has_deriv_at.matrix_kronecker {X : R → matrix m n R} {Y : R → matrix p q R}
  {X' : matrix m n R} {Y' : matrix p q R} {r : R}
  (hX : has_deriv_at X X' r) (hY : has_deriv_at Y Y' r) :
  has_deriv_at (λ a, (X a) ⊗ₖ (Y a)) (X' ⊗ₖ Y r + X r ⊗ₖ Y') r :=
begin
  rw has_deriv_at_matrix at ⊢ hX hY,
  rintros ⟨i, i'⟩ ⟨j, j'⟩,
  exact (hX _ _).mul (hY _ _),
end

lemma has_deriv_at.matrix_hadamard {X Y : R → matrix m n R}
  {X' Y' : matrix m n R} {r : R}
  (hX : has_deriv_at X X' r) (hY : has_deriv_at Y Y' r) :
  has_deriv_at (λ a, (X a) ⊙ (Y a)) (X' ⊙ Y r + X r ⊙ Y') r :=
begin
  rw has_deriv_at_matrix at ⊢ hX hY,
  rintros i j,
  exact (hX _ _).mul (hY _ _),
end

lemma has_deriv_at.trace {X : R → matrix m m R} {X' : matrix m m R} {r : R}
  (hX : has_deriv_at X X' r) :
  has_deriv_at (λ a, (X a).trace) X'.trace r :=
has_deriv_at.sum $ λ i hi, (has_deriv_at_matrix.mp hX : _) i i

lemma has_deriv_at.transpose {X : R → matrix m n R} {X' : matrix m n R} {r : R}
  (hX : has_deriv_at X X' r) :
  has_deriv_at (λ a, (X a)ᵀ) X'ᵀ r :=
has_deriv_at_matrix.mpr $ λ i j, (has_deriv_at_matrix.mp hX : _) j i

-- This is only about the elementwise norm...
lemma deriv_matrix (f : R → matrix m n R) (r : R) (hX : differentiable_at R f r) :
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