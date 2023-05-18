import analysis.calculus.deriv
import analysis.matrix
import data.matrix.kronecker
import data.matrix.hadamard
import linear_algebra.matrix.nonsingular_inverse
import linear_algebra.matrix.trace
import analysis.normed.field.basic

import matrix_cookbook.for_mathlib.analysis.matrix

/-! # Derivatives -/

variables {ι : Type*} {R : Type*} {m n p : Type*}
variables [fintype m] [fintype n] [fintype p]
variables [decidable_eq m] [decidable_eq n] [decidable_eq p]

namespace matrix_cookbook

variables [nontrivially_normed_field R]

-- this should work but gives timeouts
local attribute [instance] matrix.normed_add_comm_group matrix.normed_space
-- `matrix.normed_space` is about `semi_normed_group` which massively impacts the performance of
-- typeclass search in later lemmas.
local attribute [instance]
def matrix_field_normed_space : normed_space R (matrix m n R) :=
by exact matrix.normed_space

open_locale matrix kronecker
open matrix

/-! TODO: is this what is actually meant by `∂(XY) = (∂X)Y + X(∂Y)`? -/

lemma eq_33 (A : matrix m n R) : deriv (λ x : R, A) = 0 := deriv_const' _
lemma eq_34 (c : R) (X : R → matrix m n R) (hX : differentiable R X) :
  deriv (c • X) = c • deriv X := funext $ λ _, deriv_const_smul c (hX _)
lemma eq_35 (X Y : R → matrix m n R) (hX : differentiable R X) (hY : differentiable R Y) :
  deriv (X + Y) = deriv X + deriv Y := funext $ λ _, deriv_add (hX _) (hY _)
lemma eq_36 (X : R → matrix m m R) (hX : differentiable R X) :
  deriv (λ a, trace (X a)) = λ a, trace (deriv X a) :=
funext $ λ _, (hX _).has_deriv_at.trace.deriv
lemma eq_37 (X : R → matrix m n R) (Y : R → matrix n p R) (hX : differentiable R X) (hY : differentiable R Y) :
  deriv (λ a, (X a) ⬝ (Y a)) = λ a, deriv X a ⬝ Y a + X a ⬝ deriv Y a :=
funext $ λ a, ((hX a).has_deriv_at.matrix_mul (hY a).has_deriv_at).deriv
lemma eq_38 (X Y : R → matrix n p R) (hX : differentiable R X) (hY : differentiable R Y) :
  deriv (λ a, (X a) ⊙ (Y a)) = λ a, deriv X a ⊙ Y a + X a ⊙ deriv Y a := sorry
lemma eq_39 (X Y : R → matrix n p R) (hX : differentiable R X) (hY : differentiable R Y) :
  deriv (λ a, (X a) ⊗ₖ (Y a)) = λ a, deriv X a ⊗ₖ Y a + X a ⊗ₖ deriv Y a := sorry
lemma eq_40 (X : R → matrix n n R) (hX : differentiable R X) :
  deriv (λ a, (X a)⁻¹) = λ a, -(X a)⁻¹ * deriv X a * (X a)⁻¹ := sorry
lemma eq_41 (X : R → matrix n n R) (hX : differentiable R X) :
  deriv (λ a, det (X a)) = λ a, trace (adjugate (X a) * deriv X a) := sorry
lemma eq_42 (X : R → matrix n n R) (hX : differentiable R X) :
  deriv (λ a, det (X a)) = λ a, det (X a) • trace ((X a)⁻¹ * deriv X a) := sorry
lemma eq_43 (X : ℝ → matrix n n ℝ) (hX : differentiable ℝ X) :
  deriv (λ a, real.log (det (X a))) = λ a, trace ((X a)⁻¹ * deriv X a) := sorry
lemma eq_44 (X : R → matrix m n R) (hX : differentiable R X) :
  deriv (λ a, (X a)ᵀ) = λ a, (deriv X a)ᵀ := sorry
lemma eq_45 [star_ring R] (X : R → matrix m n R) (hX : differentiable R X) :
  deriv (λ a, (X a)ᴴ) = λ a, (deriv X a)ᴴ := sorry

/-! ## Derivatives of a Determinant -/

/-! ### General form -/

lemma eq_46 (X : R → matrix n n R) (hX : differentiable R X) :
  deriv (λ a, det (X a)) = λ a, det (X a) • trace ((X a)⁻¹ * deriv X a) := eq_42 X hX  -- this suggests we might have 42 stated strangely

-- lemma eq_47 : sorry := sorry
-- lemma eq_48 : sorry := sorry

/-! ### Linear forms -/

-- lemma eq_49 : sorry := sorry
-- lemma eq_50 : sorry := sorry
-- lemma eq_51 : sorry := sorry

/-! ### Square forms -/

-- lemma eq_52 : sorry := sorry
-- lemma eq_53 : sorry := sorry
-- lemma eq_54 : sorry := sorry

/-! ### Other nonlinear forms -/

-- lemma eq_55 : sorry := sorry
-- lemma eq_56 : sorry := sorry
-- lemma eq_57 : sorry := sorry
-- lemma eq_58 : sorry := sorry

/-! ## Derivatives of an Inverse -/

-- lemma eq_59 : sorry := sorry
-- lemma eq_60 : sorry := sorry
-- lemma eq_61 : sorry := sorry
-- lemma eq_62 : sorry := sorry
-- lemma eq_63 : sorry := sorry
-- lemma eq_64 : sorry := sorry

/-! ## Derivatives of Eigenvalues -/

-- lemma eq_65 : sorry := sorry
-- lemma eq_66 : sorry := sorry
-- lemma eq_67 : sorry := sorry
-- lemma eq_68 : sorry := sorry

/-! ## Derivatives of Matrices, Vectors, and Scalar forms -/

/-! ### First order -/

-- lemma eq_69 : sorry := sorry
-- lemma eq_70 : sorry := sorry
-- lemma eq_71 : sorry := sorry
-- lemma eq_72 : sorry := sorry
-- lemma eq_73 : sorry := sorry
-- lemma eq_74 : sorry := sorry
-- lemma eq_75 : sorry := sorry

/-! ### Second order -/

-- lemma eq_76 : sorry := sorry
-- lemma eq_77 : sorry := sorry
-- lemma eq_78 : sorry := sorry
-- lemma eq_79 : sorry := sorry
-- lemma eq_80 : sorry := sorry
-- lemma eq_81 : sorry := sorry
-- lemma eq_82 : sorry := sorry
-- lemma eq_83 : sorry := sorry
-- lemma eq_84 : sorry := sorry
-- lemma eq_85 : sorry := sorry
-- lemma eq_86 : sorry := sorry
-- lemma eq_87 : sorry := sorry
-- lemma eq_88 : sorry := sorry
-- lemma eq_89 : sorry := sorry

/-! ### Higher order and non-linear -/

-- lemma eq_90 : sorry := sorry
-- lemma eq_91 : sorry := sorry
-- lemma eq_92 : sorry := sorry
-- lemma eq_93 : sorry := sorry
-- lemma eq_94 : sorry := sorry
-- lemma eq_95 : sorry := sorry

/-! ### Gradient and hessian -/

-- lemma eq_96 : sorry := sorry
-- lemma eq_97 : sorry := sorry
-- lemma eq_98 : sorry := sorry

/-! ## Derivatives of Traces -/

/-! ### First order -/

-- lemma eq_99 : sorry := sorry
-- lemma eq_100 : sorry := sorry
-- lemma eq_101 : sorry := sorry
-- lemma eq_102 : sorry := sorry
-- lemma eq_103 : sorry := sorry
-- lemma eq_104 : sorry := sorry
-- lemma eq_105 : sorry := sorry

/-! ### Second order -/

-- eqs 106-120

/-! ### Higher order -/

-- lemma eq_121 : sorry := sorry
-- lemma eq_122 : sorry := sorry
-- lemma eq_123 : sorry := sorry

/-! ### Other -/

-- lemma eq_124 : sorry := sorry
-- lemma eq_125 : sorry := sorry
-- lemma eq_126 : sorry := sorry
-- lemma eq_127 : sorry := sorry
-- lemma eq_128 : sorry := sorry

/-! ## Derivatives of Vector norms -/

/-! ### Two-norm -/

-- lemma eq_129 : sorry := sorry
-- lemma eq_130 : sorry := sorry
-- lemma eq_131 : sorry := sorry

/-! ## Derivatives of matrix norms -/

/-! ### Frobenius norm -/

-- lemma eq_132 : sorry := sorry

/-! ## Derivatives of structured matrices -/

-- lemma eq_133 : sorry := sorry
-- lemma eq_134 : sorry := sorry

/-! ### The Chain Rule -/

-- lemma eq_135 : sorry := sorry
-- lemma eq_136 : sorry := sorry
-- lemma eq_147 : sorry := sorry

/-! ### Symmetric -/

-- lemma eq_138 : sorry := sorry
-- lemma eq_139 : sorry := sorry
-- lemma eq_140 : sorry := sorry
-- lemma eq_141 : sorry := sorry

/-! ### Diagonal -/

-- lemma eq_142 : sorry := sorry

/-! ### Toeplitz -/

-- lemma eq_143 : sorry := sorry
-- lemma eq_144 : sorry := sorry

end matrix_cookbook