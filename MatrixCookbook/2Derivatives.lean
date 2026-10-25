import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Matrix
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Hadamard
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Normed.Field.Basic
import MatrixCookbook.ForMathlib.Analysis.Matrix

/-! # Derivatives -/


variable {ι : Type _} {R : Type _} {m n p q : Type _}

variable [Fintype m] [Fintype n] [Fintype p] [Fintype q]

variable [DecidableEq m] [DecidableEq n] [DecidableEq p] [DecidableEq q]

namespace MatrixCookbook

variable [NontriviallyNormedField R]

-- this should work but gives timeouts
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

-- `matrix.normed_space` is about `semi_normed_group` which massively impacts the performance of
-- typeclass search in later lemmas.
@[local instance]
def matrixFieldNormedSpace : NormedSpace R (Matrix m n R) :=
  Matrix.normedSpace

open scoped Matrix Kronecker

open Matrix

/-! TODO: is this what is actually meant by `∂(XY) = (∂X)Y + X(∂Y)`? -/


theorem eq_33 (A : Matrix m n R) : (deriv fun _ : R => A) = 0 :=
  deriv_const' _

theorem eq_34 (c : R) (X : R → Matrix m n R) (hX : Differentiable R X) :
    deriv (c • X) = c • deriv X :=
  funext fun _ => deriv_const_smul c (hX _)

theorem eq_35 (X Y : R → Matrix m n R) (hX : Differentiable R X) (hY : Differentiable R Y) :
    deriv (X + Y) = deriv X + deriv Y :=
  funext fun _ => deriv_add (hX _) (hY _)

theorem eq_36 (X : R → Matrix m m R) (hX : Differentiable R X) :
    (deriv fun a => trace (X a)) = fun a => trace (deriv X a) :=
  funext fun _ => (hX _).hasDerivAt.trace.deriv

theorem eq_37 (X : R → Matrix m n R) (Y : R → Matrix n p R) (hX : Differentiable R X)
    (hY : Differentiable R Y) :
    (deriv fun a => X a * Y a) = fun a => deriv X a * Y a + X a * deriv Y a :=
  funext fun a => ((hX a).hasDerivAt.matrix_mul (hY a).hasDerivAt).deriv

theorem eq_38 (X Y : R → Matrix n p R) (hX : Differentiable R X) (hY : Differentiable R Y) :
    (deriv fun a => X a ⊙ Y a) = fun a => deriv X a ⊙ Y a + X a ⊙ deriv Y a :=
  funext fun a => ((hX a).hasDerivAt.matrix_hadamard (hY a).hasDerivAt).deriv

theorem eq_39 (X : R → Matrix m n R) (Y : R → Matrix p q R) (hX : Differentiable R X)
    (hY : Differentiable R Y) :
    (deriv fun a => X a ⊗ₖ Y a) = fun a => deriv X a ⊗ₖ Y a + X a ⊗ₖ deriv Y a :=
  funext fun a => ((hX a).hasDerivAt.matrix_kronecker (hY a).hasDerivAt).deriv

section

attribute [-instance] Matrix.normedAddCommGroup Matrix.normedSpace

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra

variable [CompleteSpace R]

-- porting note: added
local instance : NormedSpace R (Matrix n n R) := NormedAlgebra.toNormedSpace _

theorem eq_40 (X : R → Matrix n n R) (hX : Differentiable R X) (hX' : ∀ a, IsUnit (X a)) :
    (deriv fun a => (X a)⁻¹) = fun a => -(X a)⁻¹ * deriv X a * (X a)⁻¹ :=
  funext fun a => ((hX a).hasDerivAt.matrix_inv (hX' a)).deriv

end

theorem eq_41 (X : R → Matrix n n R) (hX : Differentiable R X) :
    (deriv fun a => det (X a)) = fun a => trace (adjugate (X a) * deriv X a) :=
  sorry

theorem eq_42 (X : R → Matrix n n R) (hX : Differentiable R X) :
    (deriv fun a => det (X a)) = fun a => det (X a) • trace ((X a)⁻¹ * deriv X a) :=
  sorry

theorem eq_43 (X : ℝ → Matrix n n ℝ) (hX : Differentiable ℝ X) :
    (deriv fun a => Real.log (det (X a))) = fun a => trace ((X a)⁻¹ * deriv X a) :=
  sorry

theorem eq_44 (X : R → Matrix m n R) (hX : Differentiable R X) :
    (deriv fun a => (X a)ᵀ) = fun a => (deriv X a)ᵀ :=
  funext fun _ => (hX _).hasDerivAt.transpose.deriv

theorem eq_45 (X : ℝ → Matrix m n ℂ) (hX : Differentiable ℝ X) :
    (deriv fun a => (X a)ᴴ) = fun a => (deriv X a)ᴴ :=
  funext fun _ => (hX _).hasDerivAt.conjTranspose.deriv

/-! ## Derivatives of a Determinant -/


/-! ### General form -/


theorem eq_46 (X : R → Matrix n n R) (hX : Differentiable R X) :
    (deriv fun a => det (X a)) = fun a => det (X a) • trace ((X a)⁻¹ * deriv X a) :=
  eq_42 X hX

/-! ### Linear forms -/


/-! ### Square forms -/


/-! ### Other nonlinear forms -/


/-! ## Derivatives of an Inverse -/


/-! ## Derivatives of Eigenvalues -/


/-! ## Derivatives of Matrices, Vectors, and Scalar forms -/


/-! ### First order -/


/-! ### Second order -/


/-! ### Higher order and non-linear -/


/-! ### Gradient and hessian -/


/-! ## Derivatives of Traces -/


/-! ### First order -/


/-! ### Second order -/


/-! ### Higher order -/


/-! ### Other -/


/-! ## Derivatives of Vector norms -/


/-! ### Two-norm -/


/-! ## Derivatives of matrix norms -/


/-! ### Frobenius norm -/


/-! ## Derivatives of structured matrices -/


/-! ### The Chain Rule -/


/-! ### Symmetric -/


/-! ### Diagonal -/


/-! ### Toeplitz -/


-- this suggests we might have 42 stated strangely
-- lemma eq_47 : (sorry : Prop) := sorry
-- lemma eq_48 : (sorry : Prop) := sorry
-- lemma eq_49 : (sorry : Prop) := sorry
-- lemma eq_50 : (sorry : Prop) := sorry
-- lemma eq_51 : (sorry : Prop) := sorry
-- lemma eq_52 : (sorry : Prop) := sorry
-- lemma eq_53 : (sorry : Prop) := sorry
-- lemma eq_54 : (sorry : Prop) := sorry
-- lemma eq_55 : (sorry : Prop) := sorry
-- lemma eq_56 : (sorry : Prop) := sorry
-- lemma eq_57 : (sorry : Prop) := sorry
-- lemma eq_58 : (sorry : Prop) := sorry
-- lemma eq_59 : (sorry : Prop) := sorry
-- lemma eq_60 : (sorry : Prop) := sorry
-- lemma eq_61 : (sorry : Prop) := sorry
-- lemma eq_62 : (sorry : Prop) := sorry
-- lemma eq_63 : (sorry : Prop) := sorry
-- lemma eq_64 : (sorry : Prop) := sorry
-- lemma eq_65 : (sorry : Prop) := sorry
-- lemma eq_66 : (sorry : Prop) := sorry
-- lemma eq_67 : (sorry : Prop) := sorry
-- lemma eq_68 : (sorry : Prop) := sorry
-- lemma eq_69 : (sorry : Prop) := sorry
-- lemma eq_70 : (sorry : Prop) := sorry
-- lemma eq_71 : (sorry : Prop) := sorry
-- lemma eq_72 : (sorry : Prop) := sorry
-- lemma eq_73 : (sorry : Prop) := sorry
-- lemma eq_74 : (sorry : Prop) := sorry
-- lemma eq_75 : (sorry : Prop) := sorry
-- lemma eq_76 : (sorry : Prop) := sorry
-- lemma eq_77 : (sorry : Prop) := sorry
-- lemma eq_78 : (sorry : Prop) := sorry
-- lemma eq_79 : (sorry : Prop) := sorry
-- lemma eq_80 : (sorry : Prop) := sorry
-- lemma eq_81 : (sorry : Prop) := sorry
-- lemma eq_82 : (sorry : Prop) := sorry
-- lemma eq_83 : (sorry : Prop) := sorry
-- lemma eq_84 : (sorry : Prop) := sorry
-- lemma eq_85 : (sorry : Prop) := sorry
-- lemma eq_86 : (sorry : Prop) := sorry
-- lemma eq_87 : (sorry : Prop) := sorry
-- lemma eq_88 : (sorry : Prop) := sorry
-- lemma eq_89 : (sorry : Prop) := sorry
-- lemma eq_90 : (sorry : Prop) := sorry
-- lemma eq_91 : (sorry : Prop) := sorry
-- lemma eq_92 : (sorry : Prop) := sorry
-- lemma eq_93 : (sorry : Prop) := sorry
-- lemma eq_94 : (sorry : Prop) := sorry
-- lemma eq_95 : (sorry : Prop) := sorry
-- lemma eq_96 : (sorry : Prop) := sorry
-- lemma eq_97 : (sorry : Prop) := sorry
-- lemma eq_98 : (sorry : Prop) := sorry
-- lemma eq_99 : (sorry : Prop) := sorry
-- lemma eq_100 : (sorry : Prop) := sorry
-- lemma eq_101 : (sorry : Prop) := sorry
-- lemma eq_102 : (sorry : Prop) := sorry
-- lemma eq_103 : (sorry : Prop) := sorry
-- lemma eq_104 : (sorry : Prop) := sorry
-- lemma eq_105 : (sorry : Prop) := sorry
-- eqs 106-120
-- lemma eq_121 : (sorry : Prop) := sorry
-- lemma eq_122 : (sorry : Prop) := sorry
-- lemma eq_123 : (sorry : Prop) := sorry
-- lemma eq_124 : (sorry : Prop) := sorry
-- lemma eq_125 : (sorry : Prop) := sorry
-- lemma eq_126 : (sorry : Prop) := sorry
-- lemma eq_127 : (sorry : Prop) := sorry
-- lemma eq_128 : (sorry : Prop) := sorry
-- lemma eq_129 : (sorry : Prop) := sorry
-- lemma eq_130 : (sorry : Prop) := sorry
-- lemma eq_131 : (sorry : Prop) := sorry
-- lemma eq_132 : (sorry : Prop) := sorry
-- lemma eq_133 : (sorry : Prop) := sorry
-- lemma eq_134 : (sorry : Prop) := sorry
-- lemma eq_135 : (sorry : Prop) := sorry
-- lemma eq_136 : (sorry : Prop) := sorry
-- lemma eq_147 : (sorry : Prop) := sorry
-- lemma eq_138 : (sorry : Prop) := sorry
-- lemma eq_139 : (sorry : Prop) := sorry
-- lemma eq_140 : (sorry : Prop) := sorry
-- lemma eq_141 : (sorry : Prop) := sorry
-- lemma eq_142 : (sorry : Prop) := sorry
-- lemma eq_143 : (sorry : Prop) := sorry
-- lemma eq_144 : (sorry : Prop) := sorry
end MatrixCookbook
